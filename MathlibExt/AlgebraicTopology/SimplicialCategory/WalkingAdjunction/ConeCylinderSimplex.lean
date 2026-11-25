/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality
public import MathlibExt.AlgebraicTopology.SimplexCategory.IntervalRepresentation
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# The actual simplex cylinder-to-cone maps

The monotone map on original ordinal products sends `(i,0)` to the
same original vertex and `(i,1)` to the new last vertex. Its ordinary
nerve defines the whole simplicial cylinder map. All original scalar
operators commute with it; the two native cylinder endpoints are the
original base inclusion and the new apex. The existing top-extension
operator is reused for the ordinal-sum comparison.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SSet.WalkingAdjunction.ConeCylinder

/-- The original product-order map fixing the base and sending the other endpoint to the new apex. -/
def collapseOrder (n : ℕ) : Fin (n + 1) × Fin 2 →o Fin (n + 2) where
  toFun p := if p.2 = 0 then p.1.castSucc else Fin.last (n + 1)
  monotone' p q hpq := by
    by_cases hp : p.2 = 0
    · by_cases hq : q.2 = 0
      · simp only [hp, hq, ite_eq_left]
        exact Fin.castSucc_le_castSucc_iff.mpr hpq.1
      · simp only [hp, hq, ite_eq_left, ite_false]
        exact Fin.le_last _
    · by_cases hq : q.2 = 0
      · have hp0 : p.2 = 0 := le_antisymm (hq ▸ hpq.2) (Fin.zero_le _)
        exact (hp hp0).elim
      · simp only [hp, hq, ite_false]
        exact le_rfl

/-- The actual ordinary functor on the same lifted ordinal objects and product arrows. -/
def collapseFunctor (n : ℕ) :
    ULift.{u} (Fin (n + 1) × Fin 2) ⥤ ULift.{u} (Fin (n + 2)) :=
  (show Monotone (fun p : ULift.{u} (Fin (n + 1) × Fin 2) => ULift.up (collapseOrder n p.down)) from
    fun _p _q hpq => (collapseOrder n).monotone hpq).functor

/-- The whole original standard-simplex cylinder map, obtained through the canonical ordinal nerves. -/
def simplexCollapse (n : ℕ) : (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[n + 1] :=
  (prodStdSimplex.isoNerve n 1).hom ≫ nerveMap (collapseFunctor n) ≫ (SSet.stdSimplex.isoNerve (n + 1)).inv

/-- The actual map retains each original base vertex and its distinct new last vertex. -/
theorem simplexCollapse_apply (n m : ℕ) (s : (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋m⦌) (i : Fin (m + 1)) :
    (simplexCollapse n).app _ s i = if s.2 i = 0 then (s.1 i).castSucc else Fin.last (n + 1) := rfl

/-- The existing extended operator, regarded as its actual simplex-category morphism. -/
abbrev extendedHom {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) : ⦋m + 1⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.mkHom (SimplexCategory.IntervalRepresentation.extendTop θ)

/-- Extending the original operator by its fixed apex is the actual ordinal-sum map. -/
theorem extendedHom_eq_tensor {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    extendedHom θ = AugmentedSimplexCategory.tensorHomOf θ (𝟙 ⦋0⦌) := by
  have h : Join.ofHom θ ⊗ₘ 𝟙 (WithInitial.of ⦋0⦌) = Join.ofHom (extendedHom θ) := by
    apply AugmentedSimplexCategory.tensorObj_hom_ext
    · rw [AugmentedSimplexCategory.inl_comp_tensorHom]
      change θ ≫ AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌ =
        AugmentedSimplexCategory.inl' ⦋m⦌ ⦋0⦌ ≫ extendedHom θ
      rw [inl'_eq_δ_last, inl'_eq_δ_last]
      ext k : 3
      change Fin.succAbove (Fin.last (n + 1)) (θ.toOrderHom k) =
        SimplexCategory.IntervalRepresentation.extendTop θ (Fin.succAbove (Fin.last (m + 1)) k)
      rw [Fin.succAbove_last_apply, Fin.succAbove_last_apply,
        SimplexCategory.IntervalRepresentation.extendTop_castSucc]
    · rw [AugmentedSimplexCategory.inr_comp_tensorHom, Category.id_comp]
      change AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌ =
        AugmentedSimplexCategory.inr' ⦋m⦌ ⦋0⦌ ≫ extendedHom θ
      ext k : 3
      have hk : k = 0 := Fin.eq_zero k
      subst k
      simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
      rw [inr'_toOrderHom_zero, inr'_toOrderHom_zero]
      exact (SimplexCategory.IntervalRepresentation.extendTop_last θ).symm
  exact (congrArg WithInitial.down h).symm

/-- Every original simplex operator commutes with the whole cylinder map and its fixed apex. -/
theorem simplexCollapse_naturality {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (SSet.stdSimplex.map θ ▷ (Δ[1] : SSet.{u})) ≫ simplexCollapse n =
      simplexCollapse m ≫ SSet.stdSimplex.map (AugmentedSimplexCategory.tensorHomOf θ (𝟙 ⦋0⦌)) := by
  rw [← extendedHom_eq_tensor]
  ext ⟨⟨k⟩⟩ : 3
  funext s
  apply SSet.stdSimplex.ext
  intro i
  change (if s.2 i = 0 then (θ.toOrderHom (s.1 i)).castSucc else Fin.last (n + 1)) =
    SimplexCategory.IntervalRepresentation.extendTop θ
      (if s.2 i = 0 then (s.1 i).castSucc else Fin.last (m + 1))
  by_cases hi : s.2 i = 0
  · simp only [hi, ite_eq_left, SimplexCategory.IntervalRepresentation.extendTop_castSucc]
  · simp only [hi, ite_false, SimplexCategory.IntervalRepresentation.extendTop_last]

/-- The original zero cylinder endpoint is the entire old base face. -/
theorem simplexCollapse_zero (n : ℕ) : (SSet.ι₀ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]) ≫ simplexCollapse n =
    SSet.stdSimplex.δ (Fin.last (n + 1)) := by
  ext ⟨⟨m⟩⟩ : 3
  funext s
  apply SSet.stdSimplex.ext
  intro i
  change (if ((SSet.ι₀ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]).app _ s).2 i = 0
    then (s i).castSucc else Fin.last (n + 1)) = Fin.succAbove (Fin.last (n + 1)) (s i)
  change (s i).castSucc = Fin.succAbove (Fin.last (n + 1)) (s i)
  exact (Fin.succAbove_last_apply (s i)).symm

/-- The original one cylinder endpoint is the entire constant map at the new last vertex. -/
theorem simplexCollapse_one (n : ℕ) : (SSet.ι₁ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]) ≫ simplexCollapse n =
    SSet.stdSimplex.isTerminalObj₀.from Δ[n] ≫
      SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) := by
  ext ⟨⟨m⟩⟩ : 3
  funext s
  apply SSet.stdSimplex.ext
  intro i
  change (if ((SSet.ι₁ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]).app _ s).2 i = 0
    then (s i).castSucc else Fin.last (n + 1)) =
      (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌).toOrderHom
        ((SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u})).app _ s i)
  change Fin.last (n + 1) = (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌).toOrderHom
    ((SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u})).app _ s i)
  have hz : (SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u})).app _ s i = 0 := Fin.eq_zero _
  exact (inr'_toOrderHom_zero n).symm.trans
    (congrArg (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌).toOrderHom hz.symm)

end SSet.WalkingAdjunction.ConeCylinder
