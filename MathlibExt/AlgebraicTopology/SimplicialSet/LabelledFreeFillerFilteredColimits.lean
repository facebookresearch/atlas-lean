/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFillerNormalForm
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Labelled one-step attachment preserves filtered colimits

Finite presentability of each generator domain makes its whole attaching maps
factor through filtered stages and makes equality hold at a common stage.
The accepted degreewise normal form preserves the old/new summand and the
complete generator/complement tag. It therefore identifies the actual mapped
colimit cocone, without countability or finiteness assumptions on targets.

This is the finite-presentable-domain specialization of Cisinski 2006,
Proposition 1.2.35, and Cisinski 2026, Lemma 2.4.37.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace SSet.labelledFreeFiller

variable {I : Type u} {K D : I → SSet.{u}} (j : ∀ s, K s ⟶ D s)
variable [∀ s, Mono (j s)] [∀ s, IsFinitelyPresentable.{u} (K s)]

private def mappedIsColimit_obj {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c) (n : ℕ) :
    IsColimit (((evaluation _ _).obj (op ⦋n⦌)).mapCocone
      ((labelledFreeFiller j).mapCocone c)) := by
  classical
  have hobj := isColimitOfPreserves ((evaluation _ _).obj (op ⦋n⦌)) hc
  apply Types.FilteredColimit.isColimitOf
  · intro z
    obtain ⟨q, rfl⟩ := (degreewiseEquiv j c.pt n).surjective z
    rcases q with x | ⟨⟨s, a⟩, d, hd⟩
    · obtain ⟨k, x₀, hx⟩ := Types.jointly_surjective_of_isColimit hobj x
      refine ⟨k, degreewiseEquiv j (F.obj k) n (Sum.inl x₀), ?_⟩
      change degreewiseEquiv j c.pt n (Sum.inl x) =
        ((labelledFreeFiller j).map (c.ι.app k)).app (op ⦋n⦌)
          (degreewiseEquiv j (F.obj k) n (Sum.inl x₀))
      rw [degreewiseEquiv_naturality]
      change degreewiseEquiv j c.pt n (Sum.inl x) =
        degreewiseEquiv j c.pt n (Sum.inl ((c.ι.app k).app (op ⦋n⦌) x₀))
      change (c.ι.app k).app (op ⦋n⦌) x₀ = x at hx
      rw [hx]
    · obtain ⟨k, a₀, ha⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc a
      refine ⟨k, degreewiseEquiv j (F.obj k) n (Sum.inr ⟨⟨s, a₀⟩, d, hd⟩), ?_⟩
      change degreewiseEquiv j c.pt n (Sum.inr ⟨⟨s, a⟩, d, hd⟩) =
        ((labelledFreeFiller j).map (c.ι.app k)).app (op ⦋n⦌)
          (degreewiseEquiv j (F.obj k) n (Sum.inr ⟨⟨s, a₀⟩, d, hd⟩))
      rw [degreewiseEquiv_naturality]
      change degreewiseEquiv j c.pt n (Sum.inr ⟨⟨s, a⟩, d, hd⟩) =
        degreewiseEquiv j c.pt n (Sum.inr ⟨⟨s, a₀ ≫ c.ι.app k⟩, d, hd⟩)
      rw [ha]
  · intro k l z z' h
    obtain ⟨q, rfl⟩ := (degreewiseEquiv j (F.obj k) n).surjective z
    obtain ⟨q', rfl⟩ := (degreewiseEquiv j (F.obj l) n).surjective z'
    change ((labelledFreeFiller j).map (c.ι.app k)).app (op ⦋n⦌)
      (degreewiseEquiv j (F.obj k) n q) =
        ((labelledFreeFiller j).map (c.ι.app l)).app (op ⦋n⦌)
          (degreewiseEquiv j (F.obj l) n q') at h
    change ∃ (m : J) (f : k ⟶ m) (g : l ⟶ m),
      ((labelledFreeFiller j).map (F.map f)).app (op ⦋n⦌)
        (degreewiseEquiv j (F.obj k) n q) =
          ((labelledFreeFiller j).map (F.map g)).app (op ⦋n⦌)
            (degreewiseEquiv j (F.obj l) n q')
    rw [degreewiseEquiv_naturality, degreewiseEquiv_naturality] at h
    have heq := (degreewiseEquiv j c.pt n).injective h
    rcases q with x | ⟨⟨s, a⟩, d, hd⟩
    · rcases q' with x' | ⟨⟨s', a'⟩, d', hd'⟩
      · have hx : (c.ι.app k).app (op ⦋n⦌) x =
            (c.ι.app l).app (op ⦋n⦌) x' := Sum.inl.inj heq
        have hxobj : (((evaluation _ _).obj (op ⦋n⦌)).mapCocone c).ι.app k x =
            (((evaluation _ _).obj (op ⦋n⦌)).mapCocone c).ι.app l x' := hx
        obtain ⟨m, f, g, hm⟩ :=
          (Types.FilteredColimit.isColimit_eq_iff _ hobj (i := k) (j := l)).mp hxobj
        refine ⟨m, f, g, ?_⟩
        rw [degreewiseEquiv_naturality, degreewiseEquiv_naturality]
        change degreewiseEquiv j (F.obj m) n (Sum.inl _) =
          degreewiseEquiv j (F.obj m) n (Sum.inl _)
        change (F.map f).app (op ⦋n⦌) x = (F.map g).app (op ⦋n⦌) x' at hm
        rw [hm]
      · cases heq
    · rcases q' with x' | ⟨⟨s', a'⟩, d', hd'⟩
      · cases heq
      · have hlabel := congrArg Sigma.fst (Sum.inr.inj heq)
        obtain rfl : s = s' := congrArg Sigma.fst hlabel
        have ha : a ≫ c.ι.app k = a' ≫ c.ι.app l := by simpa using hlabel
        have hd_eq : (⟨d, hd⟩ : {d : D s _⦋n⦌ //
            d ∉ Set.range ((j s).app (op ⦋n⦌))}) = ⟨d', hd'⟩ := by
          have hsigma := Sum.inr.inj heq
          change (⟨⟨s, a ≫ c.ι.app k⟩, ⟨d, hd⟩⟩ : Σ x : Index K c.pt,
            {d : D x.1 _⦋n⦌ // d ∉ Set.range ((j x.1).app (op ⦋n⦌))}) =
              ⟨⟨s, a' ≫ c.ι.app l⟩, ⟨d', hd'⟩⟩ at hsigma
          rw [ha] at hsigma
          simpa using hsigma
        cases hd_eq
        obtain ⟨m, f, g, hm⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hc a a' ha
        refine ⟨m, f, g, ?_⟩
        rw [degreewiseEquiv_naturality, degreewiseEquiv_naturality]
        change degreewiseEquiv j (F.obj m) n (Sum.inr ⟨⟨s, a ≫ F.map f⟩, d, hd⟩) =
          degreewiseEquiv j (F.obj m) n (Sum.inr ⟨⟨s, a' ≫ F.map g⟩, d, hd⟩)
        rw [hm]

private def mappedIsColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((labelledFreeFiller j).mapCocone c) := by
  apply evaluationJointlyReflectsColimits
  rintro ⟨⟨n⟩⟩
  exact mappedIsColimit_obj j hc n

/-- Labelled attachment along monomorphisms with finitely presentable domains
preserves all filtered colimits in the simplicial value universe. -/
instance preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u, u} (labelledFreeFiller j) where
  preserves_filtered_colimits _ _ _ :=
    { preservesColimit := ⟨fun hc => ⟨mappedIsColimit j hc⟩⟩ }

end SSet.labelledFreeFiller
