/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontOperators

/-!
# The full original fixed-front contraction prism

The actual last vertex is retained. Each front vertex is sent to the
original first vertex at time zero and retained at time one. This
monotone full simplex prism retains every original scalar operator and
the original front relation, rather than assuming a weak resolution.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

open FixedFrontCollapse

/-- The actual full original contraction keeps the last vertex and the time-one front. -/
def vertex (n : ℕ) (j : Fin (n + 2)) (t : Fin 2) : Fin (n + 2) :=
  if j = Fin.last (n + 1) ∨ t = 1 then j else 0

/-- The SAME actual contraction is monotone in both original full coordinates. -/
theorem vertex_monotone (n : ℕ) {j k : Fin (n + 2)} {s t : Fin 2}
    (hjk : j ≤ k) (hst : s ≤ t) : vertex n j s ≤ vertex n k t := by
  classical
  by_cases h : j = Fin.last (n + 1) ∨ s = 1
  · have hk : k = Fin.last (n + 1) ∨ t = 1 := by
      rcases h with hj | hs
      · exact Or.inl (le_antisymm (Fin.le_last k) (hj ▸ hjk))
      · right
        apply Fin.ext
        change t.val = 1
        change s.val ≤ t.val at hst
        have ht := t.isLt
        have hs' : s.val = 1 := congrArg Fin.val hs
        omega
    simp only [vertex, ite_eq_left h, ite_eq_left hk]
    exact hjk
  · rw [vertex, ite_eq_right h]
    exact Fin.zero_le _

/-- The SAME full original simplex and time parameter give their literal full contraction
simplex. -/
def simplex {n : ℕ} {q : SimplexCategoryᵒᵖ}
    (a : (Δ[n + 1] : SSet.{u}).obj q) (t : (Δ[1] : SSet.{u}).obj q) : (Δ[n + 1] : SSet.{u}).obj q :=
  SSet.stdSimplex.objMk (show Fin (q.unop.len + 1) →o Fin (n + 2) from
    { toFun i := vertex n (a.down.toOrderHom i) (t.down.toOrderHom i)
      monotone' _i _j h := vertex_monotone n (a.down.toOrderHom.monotone h)
        (t.down.toOrderHom.monotone h) })

/-- Every complete original scalar face or degeneracy commutes with the SAME full
contraction prism. -/
theorem simplex_operator {n : ℕ} {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r)
    (a : (Δ[n + 1] : SSet.{u}).obj q) (t : (Δ[1] : SSet.{u}).obj q) :
    (Δ[n + 1] : SSet.{u}).map θ (simplex a t) =
      simplex ((Δ[n + 1] : SSet.{u}).map θ a) ((Δ[1] : SSet.{u}).map θ t) := rfl

/-- The SAME full contraction retains the original complete front property. -/
theorem simplex_front {n : ℕ} {q : SimplexCategoryᵒᵖ}
    (a : (Δ[n + 1] : SSet.{u}).obj q) (ha : InFront a) (t : (Δ[1] : SSet.{u}).obj q) :
    InFront (simplex a t) := by
  intro i
  change vertex n (a.down.toOrderHom i) (t.down.toOrderHom i) ≠ Fin.last (n + 1)
  unfold vertex
  split_ifs
  · exact ha i
  · intro h
    have hv := congrArg Fin.val h
    change 0 = n + 1 at hv
    omega

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
