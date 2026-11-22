/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontVertices
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSimplexEndpoints

/-!
# Actual maps from the structural fixed-front quotient

A supplied successor-simplex map whose entire original front is a fixed
vertex factors through the actual fixed-front quotient. The resulting
map reads every original nonfront simplex unchanged and has the same
original source/target vertex images. Compatibility is proved from the
whole front restriction, not assumed as a comparison certificate.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontUniversalMap
open FixedFrontCollapse FixedFrontVertices
variable {n : ℕ} {X : SSet.{u}}

/-- An actual original front simplex factors through the supplied last-front face operator. -/
def frontPreimage {q : SimplexCategoryᵒᵖ} (a : (Δ[n + 1] : SSet.{u}).obj q) (ha : InFront a) :
    (Δ[n] : SSet.{u}).obj q :=
  SSet.stdSimplex.objMk {
    toFun i := (a.down.toOrderHom i).castPred (ha i)
    monotone' i j hij := show (a.down.toOrderHom i).castPred (ha i) ≤ (a.down.toOrderHom j).castPred (ha j)
      from a.down.toOrderHom.monotone hij }

/-- The actual front preimage reads back the entire original resolving simplex under the genuine front inclusion. -/
theorem frontPreimage_readback {q : SimplexCategoryᵒᵖ}
    (a : (Δ[n + 1] : SSet.{u}).obj q) (ha : InFront a) :
    (SSet.frontInclusion n).app q (frontPreimage a ha) = a := by
  have hF := SSet.frontInclusion_eq.{u} n
  have h := congrArg (fun f => f.app q (frontPreimage a ha)) hF
  refine h.trans ?_
  apply SSet.stdSimplex.objEquiv.injective
  ext i : 3
  change (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom ((a.down.toOrderHom i).castPred (ha i)) = a.down.toOrderHom i
  exact (Fin.succAbove_last_apply _).trans (Fin.castSucc_castPred _ (ha i))

/-- A whole fixed front restriction identifies exactly the two original front representatives of the
  structural quotient. -/
theorem front_equal (σ : (Δ[n + 1] : SSet.{u}) ⟶ X) (x : (Δ[0] : SSet.{u}) ⟶ X)
    (hFront : SSet.frontInclusion n ≫ σ = SSet.toDeltaZero (Δ[n] : SSet.{u}) ≫ x)
    {q : SimplexCategoryᵒᵖ} (a b : (Δ[n + 1] : SSet.{u}).obj q) (ha : InFront a) (hb : InFront b) :
    σ.app q a = σ.app q b := by
  have hA := congrArg (fun f => f.app q (frontPreimage a ha)) hFront
  have hB := congrArg (fun f => f.app q (frontPreimage b hb)) hFront
  have hP := frontPreimage_readback a ha
  have hQ := frontPreimage_readback b hb
  have h₀ : (SSet.toDeltaZero (Δ[n] : SSet.{u})).app q (frontPreimage a ha) =
      (SSet.toDeltaZero (Δ[n] : SSet.{u})).app q (frontPreimage b hb) := by
    induction q using Opposite.rec with
    | _ q =>
      induction q using SimplexCategory.rec with
      | _ d =>
        apply SSet.stdSimplex.ext
        intro i
        exact @Subsingleton.elim (Fin 1) inferInstance _ _
  exact (congrArg (σ.app q) hP).symm.trans
    (hA.trans ((congrArg (x.app q) h₀).trans (hB.symm.trans (congrArg (σ.app q) hQ))))

/-- The actual factorization through the finite structural fixed-front quotient. -/
def lift (σ : (Δ[n + 1] : SSet.{u}) ⟶ X) (x : (Δ[0] : SSet.{u}) ⟶ X)
    (hFront : SSet.frontInclusion n ≫ σ = SSet.toDeltaZero (Δ[n] : SSet.{u}) ≫ x) :
    FixedFrontCollapse.object.{u} n ⟶ X where
  app q := ↾fun a => _root_.Quotient.lift (σ.app q) (by
    rintro a b (rfl | hab)
    · rfl
    · exact front_equal σ x hFront a b hab.1 hab.2) a
  naturality q r θ := by
    apply ConcreteCategory.hom_ext
    intro a
    induction a using _root_.Quotient.inductionOn with
    | _ a => exact congr($(σ.naturality θ) a)

/-- The entire actual quotient factorization reads back the supplied original resolving-simplex map. -/
theorem projection_lift (σ : (Δ[n + 1] : SSet.{u}) ⟶ X) (x : (Δ[0] : SSet.{u}) ⟶ X)
    (hFront : SSet.frontInclusion n ≫ σ = SSet.toDeltaZero (Δ[n] : SSet.{u}) ≫ x) :
    projection n ≫ lift σ x hFront = σ := by ext q a; rfl

end CategoryTheory.CoherentRealization.FixedFrontUniversalMap
