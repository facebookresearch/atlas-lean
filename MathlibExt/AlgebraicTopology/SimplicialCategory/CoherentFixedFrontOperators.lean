/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontCollapse

/-!
# Actual cosimplicial operators of the fixed-front coherent resolution

The genuine right-join operator sends front simplices to front simplices
and retains the structural last vertex. It therefore acts on the actual
fixed-front quotient. The entire identity and composition equations use
the original simplex maps, with no resolution-comparison outcome.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontOperators
open FixedFrontCollapse PathMaximumOperators
variable {n m k : ℕ}

/-- Every original front vertex has its actual preimage in the front ordinal. -/
theorem front_preimage (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)) :
    ∃ i : Fin (n + 1), i.castSucc = j := ⟨j.castPred hj, Fin.castSucc_castPred j hj⟩

/-- The original right-join operator retains the actual front condition of every whole
resolving simplex. -/
theorem inFront_operator (θ : ⦋n⦌ ⟶ ⦋m⦌) {q : SimplexCategoryᵒᵖ}
    (a : (Δ[n + 1] : SSet.{u}).obj q) (ha : InFront a) :
    InFront ((SSet.stdSimplex.map (extension θ)).app q a) := by
  intro j
  obtain ⟨i, hi⟩ := front_preimage (a.down.toOrderHom j) (ha j)
  change (extension θ).toOrderHom (a.down.toOrderHom j) ≠ Fin.last (m + 1)
  rw [← hi, extension_front]
  exact ne_of_lt (Fin.castSucc_lt_last _)

/-- The genuine whole quotient operator of the fixed-front resolving simplicial set. -/
def map (θ : ⦋n⦌ ⟶ ⦋m⦌) : FixedFrontCollapse.object.{u} n ⟶ FixedFrontCollapse.object.{u} m where
  app q := ↾fun a => _root_.Quotient.map ((SSet.stdSimplex.map (extension θ)).app q) (by
    rintro a b (rfl | hab)
    · exact Or.inl rfl
    · exact Or.inr ⟨inFront_operator θ a hab.1, inFront_operator θ b hab.2⟩) a
  naturality q r ψ := by
    apply ConcreteCategory.hom_ext
    intro a
    induction a using _root_.Quotient.inductionOn with
    | _ a =>
      change _root_.Quotient.mk _ _ = _root_.Quotient.mk _ _
      exact congrArg (fun a => _root_.Quotient.mk _ a) (congr($((SSet.stdSimplex.map
        (extension θ)).naturality ψ) a))

/-- The entire original successor-simplex map is the actual projected quotient operator. -/
theorem projection_map (θ : ⦋n⦌ ⟶ ⦋m⦌) : projection.{u} n ≫ map θ =
    SSet.stdSimplex.map (extension θ) ≫ projection m := by ext q a; rfl

/-- The genuine right-join extension preserves the original identity operator. -/
theorem extension_id (n : ℕ) : extension (𝟙 ⦋n⦌) = 𝟙 ⦋n + 1⦌ := by
  ext j : 3
  cases j using Fin.lastCases with
  | last => exact extension_last _
  | cast i => exact extension_front _ i

/-- The genuine right-join extension preserves original simplex-operator composition. -/
theorem extension_comp (θ : ⦋n⦌ ⟶ ⦋m⦌) (ψ : ⦋m⦌ ⟶ ⦋k⦌) :
    extension (θ ≫ ψ) = extension θ ≫ extension ψ := by
  ext j : 3
  cases j using Fin.lastCases with
  | last =>
    change (extension (θ ≫ ψ)).toOrderHom (Fin.last (n + 1)) =
      (extension ψ).toOrderHom ((extension θ).toOrderHom (Fin.last (n + 1)))
    rw [extension_last, extension_last, extension_last]
  | cast i =>
    change (extension (θ ≫ ψ)).toOrderHom i.castSucc =
      (extension ψ).toOrderHom ((extension θ).toOrderHom i.castSucc)
    rw [extension_front, extension_front, extension_front]
    rfl

/-- The actual entire quotient identity operator fixes every original structural resolving
simplex. -/
theorem map_id (n : ℕ) : map.{u} (𝟙 ⦋n⦌) = 𝟙 (FixedFrontCollapse.object n) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro a
  induction a using _root_.Quotient.inductionOn with
  | _ a =>
    change _root_.Quotient.mk _ ((SSet.stdSimplex.map (extension (𝟙 ⦋n⦌))).app q a) = _
    have h := congrArg (fun θ => (SSet.stdSimplex.map θ).app q a) (extension_id n)
    have hI := congr($(SSet.stdSimplex.map_id ⦋n + 1⦌).app q a)
    exact (congrArg (fun a => _root_.Quotient.mk _ a) h).trans
      (congrArg (fun a => _root_.Quotient.mk _ a) hI)

/-- The actual entire fixed-front quotient preserves every original simplex-operator composite. -/
theorem map_comp (θ : ⦋n⦌ ⟶ ⦋m⦌) (ψ : ⦋m⦌ ⟶ ⦋k⦌) : map.{u} (θ ≫ ψ) = map θ ≫ map ψ := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro a
  induction a using _root_.Quotient.inductionOn with
  | _ a =>
    change _root_.Quotient.mk _ ((SSet.stdSimplex.map (extension (θ ≫ ψ))).app q a) = _
    have h := congrArg (fun θ => (SSet.stdSimplex.map θ).app q a) (extension_comp θ ψ)
    exact (congrArg (fun a => _root_.Quotient.mk _ a) h).trans rfl

end CategoryTheory.CoherentRealization.FixedFrontOperators
