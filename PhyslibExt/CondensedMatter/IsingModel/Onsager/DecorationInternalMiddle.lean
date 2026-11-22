/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationInternalEndpoint
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!

# The middle internal edge as a rank-two perturbation

Scaling the weight of the middle internal edge at a site adds a rank-two term to the
decorated-weight Kac-Ward matrix, handled by an augmented matrix.

## i. Overview

Transitions through the middle internal edge `(s, 1) - (s, 2)` connect the two sides `{east, north}`
and `{west, south}` of a site. Their contribution factors through a two-dimensional space indexed by
the side: scaling the middle weight by `t` changes the matrix by `t · U V` with `U` of size darts ×
2 and `V` of size 2 × darts. The block matrix with blocks `Λ₀`, `U`, `t V` and `0` has the same
`det (1 - ·)` as `Λ₀ + t U V`, so the middle edge can be treated as two extra states in an augmented
Kac-Ward matrix.

## ii. Key results

- `ons_decMiddleU` : the column factor of the rank-two term
- `ons_decMiddleV` : the row factor of the rank-two term
- `ons_KWmatDecorationWeightedPhase_scaleMiddle_rankTwo` : scaling the middle weight is a rank-two
  perturbation
- `ons_decMiddleAugmented` : the augmented matrix
- `ons_decMiddleAugmented_det` : its determinant

## iii. Table of contents

- A. Sides and factors
- B. The rank-two decomposition
- C. The augmented matrix

## iv. References

- None; the material is standard.

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators

/-! ## A. Sides and factors -/

/-- The side of a direction at a site: `0` for east and north, `1` for west and south. -/
def ons_decMiddleSide (mu : Fin 4) : Fin 2 :=
  if mu.val < 2 then 0 else 1

/-- The representative direction of a side: east for side `0`, west for side `1`. -/
def ons_decMiddleDir (side : Fin 2) : Fin 4 :=
  if side = 0 then 0 else 2

@[simp] lemma ons_fin3_univ :
    (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
  decide

/-- The weight of the internal edges between the middle edge and the port of direction `μ`, on the
destination side. -/
noncomputable def ons_decMiddleDestFactor
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L) (mu : Fin 4) : ℂ :=
  match mu with
  | 0 => decWeight (ons_decChainEdge site 0)
  | 1 => 1
  | 2 => 1
  | 3 => decWeight (ons_decChainEdge site 2)

/-- The weight of the internal edges between the port of direction `μ` and the middle edge, on the
source side. -/
noncomputable def ons_decMiddleSourceFactor
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L) (mu : Fin 4) : ℂ :=
  match mu with
  | 0 => 1
  | 1 => decWeight (ons_decChainEdge site 2)
  | 2 => decWeight (ons_decChainEdge site 0)
  | 3 => 1

/-- The column factor of the rank-two term: from a side of `site` to the darts leaving `site` on
that side. -/
noncomputable def ons_decMiddleU
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (omega : ℂ) (site : ZMod L × ZMod L) :
    Matrix (ons_Dart L) (Fin 2) ℂ :=
  fun d side ↦
    if d.1 = site ∧ ons_decMiddleSide d.2 = side then
      ons_decMiddleDestFactor decWeight site d.2 *
        ons_turnW omega (ons_decMiddleDir side) d.2
    else 0

/-- The row factor of the rank-two term: from the darts entering `site` to the side on which they
arrive. -/
noncomputable def ons_decMiddleV
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (omega u v : ℂ) (site : ZMod L × ZMod L) :
    Matrix (Fin 2) (ons_Dart L) ℂ :=
  fun side d ↦
    if site = ons_dirStep L d.2 d.1 ∧
        ons_decMiddleSide d.2 = side then
      decWeight (ons_decChainEdge site 1) *
        ons_dirPhase u v d.2 *
        decWeight s(d, ons_dartRev L d) *
        ons_decMiddleSourceFactor decWeight site d.2 *
        ons_turnW omega d.2 (ons_decMiddleDir side)
    else 0

/-! ## B. The rank-two decomposition -/

lemma ons_decChainPathIndices_one_mem_iff
    (a b : Fin 4) :
    (1 : Fin 3) ∈ ons_decChainPathIndices a b ↔
      ons_decMiddleSide a ≠ ons_decMiddleSide b := by
  fin_cases a <;> fin_cases b <;> decide

lemma ons_decTransitionWeight_scale_chain_one
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L) (t : ℂ)
    (d₂ d₁ : ons_Dart L) :
    ons_decTransitionWeight L
        (ons_scaleDecEdgeWeight decWeight
          (ons_decChainEdge site 1) t) d₂ d₁ =
      if d₂.1 = site ∧
          (1 : Fin 3) ∈
            ons_decChainPathIndices (d₁.2 + 2) d₂.2 then
        t * ons_decTransitionWeight L decWeight d₂ d₁
      else ons_decTransitionWeight L decWeight d₂ d₁ := by
  have hext : ons_scaleDecEdgeWeight decWeight
      (ons_decChainEdge site 1) t s(d₁, ons_dartRev L d₁) =
      decWeight s(d₁, ons_dartRev L d₁) := by
    unfold ons_scaleDecEdgeWeight
    rw [ite_eq_right]
    intro hedge
    apply ons_decChainEdge_not_external L site 1
    exact ⟨d₁, hedge.symm⟩
  have hchain (i : Fin 3) :
      ons_scaleDecEdgeWeight decWeight
          (ons_decChainEdge site 1) t
          (ons_decChainEdge d₂.1 i) =
        (if d₂.1 = site ∧ i = 1 then t else 1) *
          decWeight (ons_decChainEdge d₂.1 i) := by
    unfold ons_scaleDecEdgeWeight
    by_cases h : d₂.1 = site ∧ i = 1
    · have heq : ons_decChainEdge d₂.1 i =
          ons_decChainEdge site 1 :=
        (ons_decChainEdge_eq_iff d₂.1 site i 1).2 h
      simp [h]
    · have hne : ons_decChainEdge d₂.1 i ≠
          ons_decChainEdge site 1 := by
        intro heq
        exact h ((ons_decChainEdge_eq_iff d₂.1 site i 1).1 heq)
      simp [hne, h]
  unfold ons_decTransitionWeight
  rw [hext]
  simp_rw [hchain, Finset.prod_mul_distrib]
  by_cases hsite : d₂.1 = site
  · subst site
    by_cases hmem : (1 : Fin 3) ∈
        ons_decChainPathIndices (d₁.2 + 2) d₂.2
    · simp [hmem]
      ring
    · simp [hmem]
  · have hnone : ∀ i : Fin 3,
        ¬ (d₂.1 = site ∧ i = 1) := by
      intro i h
      exact hsite h.1
    simp [hsite]

private lemma ons_decMiddle_mul_apply_dir0
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega u v : ℂ) (homega : omega ≠ 0)
    (site : ZMod L × ZMod L)
    (d₂ : ons_Dart L) (site₁ : ZMod L × ZMod L) :
    (ons_decMiddleU L decWeight omega site *
        ons_decMiddleV L decWeight omega u v site) d₂ (site₁, 0) =
      if d₂.1 = site ∧
          (1 : Fin 3) ∈
            ons_decChainPathIndices ((0 : Fin 4) + 2) d₂.2 then
        ons_KWmatDecorationWeightedPhase L decWeight omega u v d₂ (site₁, 0)
      else 0 := by
  rcases d₂ with ⟨site₂, mu₂⟩
  by_cases hstep : site₂ = ons_dirStep L 0 site₁ <;>
    by_cases hsite : site₂ = site <;>
    fin_cases mu₂ <;>
    simp_all [ons_decMiddleU, ons_decMiddleV,
      ons_decMiddleSide, ons_decMiddleDir,
      ons_decMiddleDestFactor, ons_decMiddleSourceFactor,
      Matrix.mul_apply, ons_decTransitionWeight,
      ons_KWmatDecorationWeightedPhase,
      ons_turnW] <;> field_simp

private lemma ons_decMiddle_mul_apply_dir1
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega u v : ℂ) (homega : omega ≠ 0)
    (site : ZMod L × ZMod L)
    (d₂ : ons_Dart L) (site₁ : ZMod L × ZMod L) :
    (ons_decMiddleU L decWeight omega site *
        ons_decMiddleV L decWeight omega u v site) d₂ (site₁, 1) =
      if d₂.1 = site ∧
          (1 : Fin 3) ∈
            ons_decChainPathIndices ((1 : Fin 4) + 2) d₂.2 then
        ons_KWmatDecorationWeightedPhase L decWeight omega u v d₂ (site₁, 1)
      else 0 := by
  rcases d₂ with ⟨site₂, mu₂⟩
  by_cases hstep : site₂ = ons_dirStep L 1 site₁ <;>
    by_cases hsite : site₂ = site <;>
    fin_cases mu₂ <;>
    simp_all [ons_decMiddleU, ons_decMiddleV,
      ons_decMiddleSide, ons_decMiddleDir,
      ons_decMiddleDestFactor, ons_decMiddleSourceFactor,
      Matrix.mul_apply, ons_decTransitionWeight,
      ons_KWmatDecorationWeightedPhase,
      ons_turnW] <;> field_simp

private lemma ons_decMiddle_mul_apply_dir2
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega u v : ℂ) (homega : omega ≠ 0)
    (site : ZMod L × ZMod L)
    (d₂ : ons_Dart L) (site₁ : ZMod L × ZMod L) :
    (ons_decMiddleU L decWeight omega site *
        ons_decMiddleV L decWeight omega u v site) d₂ (site₁, 2) =
      if d₂.1 = site ∧
          (1 : Fin 3) ∈
            ons_decChainPathIndices ((2 : Fin 4) + 2) d₂.2 then
        ons_KWmatDecorationWeightedPhase L decWeight omega u v d₂ (site₁, 2)
      else 0 := by
  rcases d₂ with ⟨site₂, mu₂⟩
  by_cases hstep : site₂ = ons_dirStep L 2 site₁ <;>
    by_cases hsite : site₂ = site <;>
    fin_cases mu₂ <;>
    simp_all [ons_decMiddleU, ons_decMiddleV,
      ons_decMiddleSide, ons_decMiddleDir,
      ons_decMiddleDestFactor, ons_decMiddleSourceFactor,
      Matrix.mul_apply, ons_decTransitionWeight,
      ons_KWmatDecorationWeightedPhase,
      ons_turnW] <;> field_simp

private lemma ons_decMiddle_mul_apply_dir3
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega u v : ℂ) (homega : omega ≠ 0)
    (site : ZMod L × ZMod L)
    (d₂ : ons_Dart L) (site₁ : ZMod L × ZMod L) :
    (ons_decMiddleU L decWeight omega site *
        ons_decMiddleV L decWeight omega u v site) d₂ (site₁, 3) =
      if d₂.1 = site ∧
          (1 : Fin 3) ∈
            ons_decChainPathIndices ((3 : Fin 4) + 2) d₂.2 then
        ons_KWmatDecorationWeightedPhase L decWeight omega u v d₂ (site₁, 3)
      else 0 := by
  rcases d₂ with ⟨site₂, mu₂⟩
  by_cases hstep : site₂ = ons_dirStep L 3 site₁ <;>
    by_cases hsite : site₂ = site <;>
    fin_cases mu₂ <;>
    simp_all [ons_decMiddleU, ons_decMiddleV,
      ons_decMiddleSide, ons_decMiddleDir,
      ons_decMiddleDestFactor, ons_decMiddleSourceFactor,
      Matrix.mul_apply, ons_decTransitionWeight,
      ons_KWmatDecorationWeightedPhase,
      ons_turnW] <;> field_simp

lemma ons_decMiddle_mul_apply
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega u v : ℂ) (homega : omega ≠ 0)
    (site : ZMod L × ZMod L)
    (d₂ d₁ : ons_Dart L) :
    (ons_decMiddleU L decWeight omega site *
        ons_decMiddleV L decWeight omega u v site) d₂ d₁ =
      if d₂.1 = site ∧
          (1 : Fin 3) ∈
            ons_decChainPathIndices (d₁.2 + 2) d₂.2 then
        ons_KWmatDecorationWeightedPhase L decWeight omega u v d₂ d₁
      else 0 := by
  rcases d₁ with ⟨site₁, mu₁⟩
  fin_cases mu₁
  · exact ons_decMiddle_mul_apply_dir0
      L decWeight omega u v homega site d₂ site₁
  · exact ons_decMiddle_mul_apply_dir1
      L decWeight omega u v homega site d₂ site₁
  · exact ons_decMiddle_mul_apply_dir2
      L decWeight omega u v homega site d₂ site₁
  · exact ons_decMiddle_mul_apply_dir3
      L decWeight omega u v homega site d₂ site₁

lemma ons_KWmatDecorationWeightedPhase_scaleMiddle_rankTwo
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega u v t : ℂ) (homega : omega ≠ 0)
    (site : ZMod L × ZMod L) :
    ons_KWmatDecorationWeightedPhase L
        (ons_scaleDecEdgeWeight decWeight
          (ons_decChainEdge site 1) t) omega u v =
      ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 1) 0) omega u v +
        t • (ons_decMiddleU L decWeight omega site *
          ons_decMiddleV L decWeight omega u v site) := by
  ext d₂ d₁
  simp only [Matrix.add_apply, Matrix.smul_apply]
  unfold ons_KWmatDecorationWeightedPhase
  rw [ons_decTransitionWeight_scale_chain_one]
  rw [ons_decTransitionWeight_scale_chain_one]
  rw [ons_decMiddle_mul_apply L decWeight omega u v homega site]
  by_cases hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1 <;>
    by_cases hcross : d₂.1 = site ∧
      (1 : Fin 3) ∈
        ons_decChainPathIndices (d₁.2 + 2) d₂.2 <;>
    by_cases harr : ons_dirStep L d₁.2 d₁.1 = site <;>
    simp_all [ons_KWmatDecorationWeightedPhase] <;> ring

/-! ## C. The augmented matrix -/

/-- The augmented Kac-Ward matrix on darts and the two sides of `site`, with blocks `Λ₀`, `U`, `t V`
and `0`. -/
noncomputable def ons_decMiddleAugmented
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (omega u v t : ℂ) (site : ZMod L × ZMod L) :
    Matrix (ons_Dart L ⊕ Fin 2) (ons_Dart L ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks
    (ons_KWmatDecorationWeightedPhase L
      (ons_scaleDecEdgeWeight decWeight
        (ons_decChainEdge site 1) 0) omega u v)
    (ons_decMiddleU L decWeight omega site)
    (t • ons_decMiddleV L decWeight omega u v site)
    0

lemma ons_decMiddleAugmented_det
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ)
    (omega u v t : ℂ) (homega : omega ≠ 0)
    (site : ZMod L × ZMod L) :
    (1 - ons_decMiddleAugmented L decWeight omega u v t site).det =
      (1 - ons_KWmatDecorationWeightedPhase L
        (ons_scaleDecEdgeWeight decWeight
          (ons_decChainEdge site 1) t) omega u v).det := by
  let M₀ := ons_KWmatDecorationWeightedPhase L
    (ons_scaleDecEdgeWeight decWeight
      (ons_decChainEdge site 1) 0) omega u v
  let U := ons_decMiddleU L decWeight omega site
  let V := ons_decMiddleV L decWeight omega u v site
  have hblock :
      1 - ons_decMiddleAugmented L decWeight omega u v t site =
        Matrix.fromBlocks (1 - M₀) (-U) (-(t • V)) 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [ons_decMiddleAugmented, M₀, U, V, Matrix.one_apply]
  have hmul : (-U) * (-(t • V)) = t • (U * V) := by
    ext i j
    simp [Matrix.mul_apply]
    ring
  rw [hblock, Matrix.det_fromBlocks_one₂₂, hmul]
  have hrank :=
    ons_KWmatDecorationWeightedPhase_scaleMiddle_rankTwo
      L decWeight omega u v t homega site
  have hrank' :
      ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 1) t) omega u v =
        M₀ + t • (U * V) := by
    simpa only [M₀, U, V] using hrank
  rw [show 1 - M₀ - t • (U * V) =
      1 - (M₀ + t • (U * V)) by abel]
  rw [← hrank']

end StatMech.Onsager
