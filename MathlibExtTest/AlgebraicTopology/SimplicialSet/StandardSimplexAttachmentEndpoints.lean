/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/
module

import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexCompat
import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexAttachmentCompat
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFibrationPathComposition
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AnodyneFixedBottom

/-!
# Standard-simplex coordinates and boundary-attachment clients

The first and last cofaces of Δ[1] have distinct vertex coordinates. A simplex whose Yoneda
map is monic retains its identity and inclusion equations under the native representability
construction. Above the identity fibration of Δ[2], filling its adjacent edges yields the
middle face. A finite attachment chain also permits its two endpoints to coincide.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite Simplicial
open scoped Simplicial SSet.modelCategoryQuillen

namespace MathlibExtTest.StandardSimplexAttachmentEndpoints

universe u

example :
    ((SSet.stdSimplex.objEquiv.{0}).symm (SimplexCategory.δ (0 : Fin 2)) :
      (Δ[1] : SSet.{0}) _⦋0⦌) (0 : Fin 1) = (1 : Fin 2) :=
  SSet.stdSimplex.objEquiv_symm_δ_apply 0 0

example :
    ((SSet.stdSimplex.objEquiv.{0}).symm (SimplexCategory.δ (1 : Fin 2)) :
      (Δ[1] : SSet.{0}) _⦋0⦌) (0 : Fin 1) = (0 : Fin 2) :=
  SSet.stdSimplex.objEquiv_symm_δ_apply 1 0

example :
    ((SSet.stdSimplex.objEquiv.{0}).symm (SimplexCategory.σ (0 : Fin 1)) :
      (Δ[0] : SSet.{0}) _⦋1⦌) (1 : Fin 2) = (0 : Fin 1) :=
  SSet.stdSimplex.objEquiv_symm_σ_apply 0 1

example {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) [Mono (SSet.yonedaEquiv.symm x)] :
    dsimp% (SSet.Subcomplex.ofSimplexRepresentableBy x).homEquiv (𝟙 ⦋n⦌) = x :=
  SSet.Subcomplex.ofSimplexRepresentableBy_id x

example {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) [Mono (SSet.yonedaEquiv.symm x)] :
    (SSet.stdSimplex.isoOfRepresentableBy (SSet.Subcomplex.ofSimplexRepresentableBy x)).hom ≫
      (SSet.Subcomplex.ofSimplex x).ι = SSet.yonedaEquiv.symm x :=
  SSet.Subcomplex.isoOfRepresentableBy_ofSimplexRepresentableBy_hom x

example : ∃ e : (Δ[1] : SSet.{0}) ⟶ Δ[2],
    e = SSet.stdSimplex.δ (1 : Fin 3) ∧
      SSet.stdSimplex.δ (1 : Fin 2) ≫ e =
        SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) ∧
      SSet.stdSimplex.δ (0 : Fin 2) ≫ e =
        SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3) := by
  have hshared :
      SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
        SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3) := by
    simpa only using
      (SSet.stdSimplex.{0}).δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  obtain ⟨e, hfirst, hlast, hover⟩ :=
    SSet.exists_path_composition_above_of_fibration (𝟙 (Δ[2] : SSet.{0}))
      (SSet.stdSimplex.δ (2 : Fin 3)) (SSet.stdSimplex.δ (0 : Fin 3)) hshared
      (𝟙 (Δ[2] : SSet.{0})) (by simp) (by simp)
  exact ⟨e, by simpa only [Category.comp_id] using hover, hfirst, hlast⟩

example {X : SSet.{u}} (J : X.Subcomplex) [SSet.Finite (J : SSet.{u})] :
    ∃ (k : ℕ) (C : Fin (k + 1) → X.Subcomplex),
      C ⟨0, Nat.zero_lt_succ k⟩ = J ∧ C ⟨k, Nat.lt_succ_self k⟩ = J ∧
        (∀ i j : Fin (k + 1), i.val ≤ j.val → C i ≤ C j) := by
  obtain ⟨k, C, hfirst, hlast, hmono, _⟩ :=
    SSet.boundary.exists_finite_attachment_chain_of_le_of_finite J J (le_refl J)
  exact ⟨k, C, hfirst, hlast, hmono⟩

example {X Y E B : SSet.{u}} (i : X ⟶ Y) (hi : SSet.anodyneExtensions i)
    (p : E ⟶ B) (b : Y ⟶ B)
    (h : ∀ {n : ℕ} (σ : Δ[n + 1] ⟶ Y) (j : Fin (n + 2)),
      HasLiftingPropertyFixedBot (SSet.horn (n + 1) j).ι p (σ ≫ b))
    (a : X ⟶ E) (ha : CommSq a i p b) :
    ∃ ℓ : Y ⟶ E, i ≫ ℓ = a ∧ ℓ ≫ p = b := by
  letI := (SSet.anodyneExtensions.hasLiftingPropertyFixedBot_of_simplices hi p b h) a ha
  exact ⟨ha.lift, ha.fac_left, ha.fac_right⟩

end MathlibExtTest.StandardSimplexAttachmentEndpoints
