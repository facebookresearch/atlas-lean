/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Author: @toskua, Avocado
module

-- BACKPORT: Full-file copy of
-- `Mathlib/AlgebraicTopology/SimplicialSet/KanComplex/FundamentalGroupoid.lean`
-- from PR `leanprover-community/mathlib4#42435` head
-- `e09070f786c9fc0a688e6239d71230b618b045ff`, blob
-- `60c286e3e8d0d60ad118aba7858a5d9711000836`.
-- Import adaptations for pinned Mathlib v4.34.1
-- (`d13f23b723b8a846827a245b89c10fc7d3f11612`): canonical
-- `Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory`,
-- canonical `Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct`, and
-- canonical `Mathlib.AlgebraicTopology.SimplicialSet.KanComplex` (provides
-- `KanComplex X.op`, replacing `MathlibExt.AlgebraicTopology.SimplicialSet.KanComplexCompat`
-- and the direct `Mathlib.AlgebraicTopology.SimplicialSet.Op` import); retained
-- witness-level `MathlibExt.AlgebraicTopology.Quasicategory.TwoTruncatedCompat` for
-- `Edge.assoc`, `assoc'`, `CompStruct.unique`, and `HomotopyCategory₂.desc`
-- family declarations; retained local
-- `MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic`,
-- `MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexCompat`, and
-- `MathlibExt.AlgebraicTopology.SimplicialSet.CompStructCompat`.
-- Pinned-Mathlib adaptation (Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`): the
-- `SSet.Edge` composition block (`HomotopyL`, `HomotopyR`, `comp`, `compStruct`, `assoc`,
-- `assoc'`, `HomotopyL.homotopyR`, `HomotopyR.homotopyL`, `CompStruct.unique` and
-- `CompStruct.unique'`) is imported from canonical
-- `Mathlib.AlgebraicTopology.Quasicategory.CompStruct`, whose declarations are identical.
-- Deletion / upgrade rule: delete this `MathlibExt` module and replace its imports
-- with the canonical `Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.FundamentalGroupoid`
-- once the pinned Mathlib contains the file and all declarations; regenerate
-- `MathlibExt.lean` in a separate Avocado task and rebuild `MathlibExt`.
-- See `BACKPORTS.md` and `scratches/model-category/BLUEPRINT_1_YEAR.md`.

public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory
public import Mathlib.AlgebraicTopology.Quasicategory.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.CompStructCompat

/-!
# The fundamental groupoid of a Kan complex

...

-/

@[expose] public section

universe u

open HomotopicalAlgebra CategoryTheory Simplicial

namespace SSet

variable {X : SSet.{u}}

namespace Edge

variable [KanComplex X]

variable {x y : X _⦋0⦌} (e : Edge x y)

lemma exists_right_inverse : ∃ (e' : Edge y x), Nonempty (CompStruct e e' (.id x)) := by
  let φ (j : Fin 3) (hk : j ≠ 0) : Δ[1] ⟶ X :=
    if j = 1 then const x else yonedaEquiv.symm e.edge
  have hφ : horn.IsCompatible φ := by
    rw [horn.isCompatible_iff]
    intro j k
    fin_cases j <;> fin_cases k <;> simp [φ, yonedaEquiv_symm_zero]
  have hσ : X.σ 0 x = SSet.yonedaEquiv (SSet.const x : Δ[1] ⟶ X) := by
    apply SSet.yonedaEquiv.symm.injective
    rw [Equiv.symm_apply_apply, ← SSet.stdSimplex.σ_comp_yonedaEquiv_symm,
      SSet.yonedaEquiv_symm_zero, SSet.comp_const]
  refine ⟨Edge.mk (yonedaEquiv (stdSimplex.δ 0 ≫ hφ.liftOfKanComplex))
    (yonedaEquiv.symm.injective ?_) (yonedaEquiv.symm.injective ?_),
    ⟨Edge.CompStruct.mk (yonedaEquiv hφ.liftOfKanComplex) ?_ ?_ ?_⟩⟩
  · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
      ← dsimp% stdSimplex.δ_comp_δ_assoc (n := 0) (i := 0) (j := 1) (by simp),
      hφ.δ_liftOfKanComplex 2 (by simp), φ]
  · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
      dsimp% stdSimplex.δ_comp_δ_self_assoc (n := 0) (i := 0),
      hφ.δ_liftOfKanComplex 1 (by simp), φ, yonedaEquiv_symm_zero]
  · simp [← stdSimplex.yonedaEquiv_δ_comp, hφ.δ_liftOfKanComplex 2 (by simp), φ]
  · simp [stdSimplex.yonedaEquiv_δ_comp]
  · simp [← stdSimplex.yonedaEquiv_δ_comp, hφ.δ_liftOfKanComplex 1 (by simp), φ,
      hσ]

lemma exists_left_inverse : ∃ (e' : Edge y x), Nonempty (CompStruct e' e (.id y)) := by
  obtain ⟨e', ⟨h⟩⟩ := exists_right_inverse e.op
  exact ⟨e'.unop, ⟨h.unop.ofEq rfl rfl (by simp)⟩⟩

instance : Nonempty e.InvStruct := by
  have : KanComplex X := inferInstance
  obtain ⟨e₁, ⟨h₁⟩⟩ := e.exists_left_inverse
  obtain ⟨e₂, ⟨h₂⟩⟩ := e.exists_right_inverse
  exact ⟨{
    inv := e₁
    homInvId :=
      assoc' h₂ (HomotopyR.homotopyL (Edge.assoc h₁ h₂ (.compId _))) (.idCompId _)
    invHomId := h₁
  }⟩

/-- A choice of `Edge.InvStruct` structure in a Kan complex. -/
@[no_expose]
noncomputable def invStruct : e.InvStruct := Classical.arbitrary _

/-- A choice of inverse of an edge in a Kan complex. -/
noncomputable abbrev inv : Edge y x := e.invStruct.inv

/-- If `e` is an edge of Kan complex, then `e.inv` is a right inverse to `e`. -/
noncomputable abbrev homInvId : CompStruct e e.inv (.id x) := e.invStruct.homInvId

/-- If `e` is an edge of Kan complex, then `e.inv` is a left inverse to `e`. -/
noncomputable abbrev invHomId : CompStruct e.inv e (.id y) := e.invStruct.invHomId

end Edge

variable [KanComplex X]

namespace KanComplex

open Truncated.HomotopyCategory₂ in
instance : IsGroupoid (Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X)) where
  all_isIso := by
    rintro ⟨x : X _⦋0⦌⟩ ⟨y : X _⦋0⦌⟩ f
    obtain ⟨e, rfl⟩ := homMk_surjective f
    let γ := (Edge.ofTruncated e).invStruct
    exact ⟨homMk γ.inv, γ.homInvId.homotopyCategory₂_fac,
      γ.invHomId.homotopyCategory₂_fac⟩

noncomputable instance : Groupoid (Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X)) :=
  .ofIsGroupoid

set_option backward.isDefEq.respectTransparency.types false in
variable (X) in
open Truncated.HomotopyCategory₂ in
/-- If `X` is a Kan complex, then `Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X)`
is isomorphic to `FundamentalGroupoid X`. -/
@[implicit_reducible, simps -isSimp]
noncomputable def isoCatFundamentalGroupoid :
    IsoCat (Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X))
      (FundamentalGroupoid X) where
  functor :=
    Truncated.HomotopyCategory₂.desc
      (fun x ↦ .mk x) (fun e ↦ FundamentalGroupoid.homMk (Edge.ofTruncated e))
        FundamentalGroupoid.homMk_id Edge.CompStruct.homMk_comp
  inverse := FundamentalGroupoid.desc (fun x ↦ .mk x) (fun e ↦ homMk e.toTruncated)
    (fun h ↦ h.homotopyCategory₂_fac)
  unit_eq := by
    apply CategoryTheory.Functor.ext (h_obj := ?_) (h_map := ?_)
    · intro x
      rcases x with ⟨x⟩
      with_unfolding_all rfl
    · intro x y f
      obtain ⟨e, rfl⟩ := homMk_surjective f
      simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map,
        Truncated.HomotopyCategory₂.desc_map_homMk,
        SSet.FundamentalGroupoid.desc_map_homMk,
        SSet.Edge.toTruncated_ofTruncated,
        CategoryTheory.eqToHom_refl, Category.comp_id, Category.id_comp]
  counit_eq := by
    apply SSet.FundamentalGroupoid.functor_ext (h₁ := ?_) (h₂ := ?_)
    · intro x
      with_unfolding_all rfl
    · intro x y e
      simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map,
        SSet.FundamentalGroupoid.desc_map_homMk,
        Truncated.HomotopyCategory₂.desc_map_homMk,
        SSet.Edge.ofTruncated_toTruncated,
        CategoryTheory.eqToHom_refl, Category.comp_id, Category.id_comp]

variable (X) in
/-- If `X` is a Kan complex, then `Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X)`
is equivalent to `FundamentalGroupoid X`. -/
noncomputable abbrev equivalenceFundamentalGroupoid :
    Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X) ≌
      (FundamentalGroupoid X) :=
  (isoCatFundamentalGroupoid X).toEquivalence

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma isoCatFundamentalGroupoid_functor_map_homMk
    {x y : X _⦋0⦌} (e : Edge x y) :
    (isoCatFundamentalGroupoid X).functor.map (Truncated.HomotopyCategory₂.homMk e.toTruncated) =
      FundamentalGroupoid.homMk e := by
  simp [isoCatFundamentalGroupoid_functor, SSet.Edge.ofTruncated_toTruncated]

end KanComplex

namespace FundamentalGroupoid

open KanComplex

set_option backward.isDefEq.respectTransparency.types false in
lemma homMk_surjective {x y : X _⦋0⦌} :
    Function.Surjective (homMk : Edge x y → _) := by
  intro f
  obtain ⟨f, rfl⟩ := (isoCatFundamentalGroupoid X).functor.map_surjective f
  obtain ⟨e, rfl⟩ := Truncated.HomotopyCategory₂.homMk_surjective f
  exact ⟨Edge.ofTruncated e, by simp [isoCatFundamentalGroupoid_functor]⟩

@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma hom_rec_of_kanComplex {x y : X _⦋0⦌} (motive : (mk x ⟶ mk y) → Prop)
    (homMk : ∀ (e : Edge x y), motive (homMk e)) (f : mk x ⟶ mk y) :
    motive f := by
  obtain ⟨e, rfl⟩ := homMk_surjective f
  exact homMk e

lemma homMk_eq_iff_nonempty_homotopyL {x y : X _⦋0⦌} {e e' : Edge x y} :
    homMk e = homMk e' ↔ Nonempty (Edge.HomotopyL e e') := by
  calc homMk e = homMk e' ↔
      (isoCatFundamentalGroupoid X).functor.map
          (Truncated.HomotopyCategory₂.homMk e.toTruncated) =
        (isoCatFundamentalGroupoid X).functor.map
          (Truncated.HomotopyCategory₂.homMk e'.toTruncated) := by
        simp only [isoCatFundamentalGroupoid_functor_map_homMk]
      _ ↔ Truncated.HomotopyCategory₂.homMk e.toTruncated =
          Truncated.HomotopyCategory₂.homMk e'.toTruncated := by
        simp only [Functor.map_injective_iff]
      _ ↔ Truncated.HomotopicL e.toTruncated e'.toTruncated := by
        exact Truncated.HomotopyCategory₂.homMk_eq_iff_homotopicL
      _ ↔ Nonempty (Edge.HomotopyL e e') := by
        with_unfolding_all rfl

lemma homMk_eq_iff_nonempty_homotopyR {x y : X _⦋0⦌} {e e' : Edge x y} :
    homMk e = homMk e' ↔ Nonempty (Edge.HomotopyR e e') := by
  rw [homMk_eq_iff_nonempty_homotopyL]
  apply Truncated.homotopicL_iff_homotopicR

lemma homMk_comp_iff {x₀ x₁ x₂ : X _⦋0⦌} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂} :
    homMk e₀₁ ≫ homMk e₁₂ = homMk e₀₂ ↔ Nonempty (Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  refine ⟨fun h ↦ ?_, fun ⟨h⟩ ↦ h.homMk_comp⟩
  rw [(Edge.compStruct e₀₁ e₁₂).homMk_comp, homMk_eq_iff_nonempty_homotopyL] at h
  obtain ⟨h⟩ := h
  exact ⟨Edge.CompStruct.unique' (Edge.compStruct e₀₁ e₁₂) h⟩

@[simp]
lemma homMk_inv {x y : X _⦋0⦌} (e : Edge x y) :
    homMk e.inv = inv (homMk e) := by
  simpa [← cancel_mono (homMk e), IsIso.inv_hom_id] using e.invHomId.homMk_comp

end FundamentalGroupoid

end SSet
