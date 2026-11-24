/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFillerNormalForm
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Labelled one-step attachment preserves pullbacks

The degreewise normal form retains the old/new summand and the fixed
generator/complement tag under every map. In a pullback, old elements use
the actual degreewise pullback and new attaching maps use its whole
morphism universal property. No monicity of the span maps is needed.

The original monic-span result is Cisinski, *Higher Categories and
Homotopical Algebra*, Lemma 2.4.37, and Cisinski 2006, Proposition 1.2.35.
The all-span extension here follows directly from the accepted labelled
normal form. Native pullback preservation supplies monomorphism
preservation; no competing instance is introduced.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace SSet.labelledFreeFiller

variable {I : Type u} {K D : I → SSet.{u}} (j : ∀ s, K s ⟶ D s)
variable [∀ s, Mono (j s)]

private lemma mappedPullback_obj {P X V Y : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ V} {f : X ⟶ Y} {g : V ⟶ Y}
    (h : IsPullback a b f g) (n : ℕ) :
    IsPullback (((labelledFreeFiller j).map a).app (op ⦋n⦌))
      (((labelledFreeFiller j).map b).app (op ⦋n⦌))
      (((labelledFreeFiller j).map f).app (op ⦋n⦌))
      (((labelledFreeFiller j).map g).app (op ⦋n⦌)) := by
  classical
  let F := labelledFreeFiller j
  have hobj := h.map ((evaluation _ _).obj (op ⦋n⦌))
  refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
  · simpa only [Functor.map_comp, NatTrans.comp_app] using
      congrArg (fun q => q.app (op ⦋n⦌)) (F.congr_map h.w)
  · intro z z' ⟨ha, hb⟩
    obtain ⟨q, rfl⟩ := (degreewiseEquiv j P n).surjective z
    obtain ⟨q', rfl⟩ := (degreewiseEquiv j P n).surjective z'
    rw [degreewiseEquiv_naturality, degreewiseEquiv_naturality] at ha hb
    have hx := (degreewiseEquiv j X n).injective ha
    have hv := (degreewiseEquiv j V n).injective hb
    rcases q with x | ⟨⟨s, c⟩, d, hd⟩
    · rcases q' with x' | ⟨⟨t, c'⟩, d', hd'⟩
      · have eq := Types.ext_of_isPullback hobj (Sum.inl.inj hx) (Sum.inl.inj hv)
        rw [eq]
      · cases hx
    · rcases q' with x' | ⟨⟨t, c'⟩, d', hd'⟩
      · cases hx
      · have hlabel := congrArg Sigma.fst (Sum.inr.inj hx)
        obtain rfl : s = t := congrArg Sigma.fst hlabel
        have hc : c ≫ a = c' ≫ a := by simpa using hlabel
        have hc' : c ≫ b = c' ≫ b := by
          simpa using congrArg Sigma.fst (Sum.inr.inj hv)
        obtain rfl : c = c' := h.hom_ext hc hc'
        have hd_eq : (⟨d, hd⟩ : {d : D s _⦋n⦌ //
            d ∉ Set.range ((j s).app (op ⦋n⦌))}) = ⟨d', hd'⟩ := by
          simpa using Sum.inr.inj hx
        cases hd_eq
        rfl
  · intro zX zV heq
    obtain ⟨qX, rfl⟩ := (degreewiseEquiv j X n).surjective zX
    obtain ⟨qV, rfl⟩ := (degreewiseEquiv j V n).surjective zV
    rw [degreewiseEquiv_naturality, degreewiseEquiv_naturality] at heq
    have hy := (degreewiseEquiv j Y n).injective heq
    rcases qX with x | ⟨⟨s, c⟩, d, hd⟩
    · rcases qV with v | ⟨⟨t, c'⟩, d', hd'⟩
      · obtain ⟨p, hpX, hpV⟩ := Types.exists_of_isPullback hobj x v (Sum.inl.inj hy)
        refine ⟨degreewiseEquiv j P n (Sum.inl p), ?_, ?_⟩
        · rw [degreewiseEquiv_naturality]
          change degreewiseEquiv j X n (Sum.inl (a.app (op ⦋n⦌) p)) = _
          rw [show a.app (op ⦋n⦌) p = x from hpX]
        · rw [degreewiseEquiv_naturality]
          change degreewiseEquiv j V n (Sum.inl (b.app (op ⦋n⦌) p)) = _
          rw [show b.app (op ⦋n⦌) p = v from hpV]
      · cases hy
    · rcases qV with v | ⟨⟨t, c'⟩, d', hd'⟩
      · cases hy
      · have hlabel := congrArg Sigma.fst (Sum.inr.inj hy)
        obtain rfl : s = t := congrArg Sigma.fst hlabel
        have hc : c ≫ f = c' ≫ g := by simpa using hlabel
        have hd_eq : (⟨d, hd⟩ : {d : D s _⦋n⦌ //
            d ∉ Set.range ((j s).app (op ⦋n⦌))}) = ⟨d', hd'⟩ := by
          have hsigma := Sum.inr.inj hy
          change (⟨⟨s, c ≫ f⟩, ⟨d, hd⟩⟩ : Σ x : Index K Y,
            {d : D x.1 _⦋n⦌ // d ∉ Set.range ((j x.1).app (op ⦋n⦌))}) =
              ⟨⟨s, c' ≫ g⟩, ⟨d', hd'⟩⟩ at hsigma
          rw [hc] at hsigma
          simpa using hsigma
        cases hd_eq
        let l := h.lift c c' hc
        have hlX : l ≫ a = c := h.lift_fst _ _ _
        have hlV : l ≫ b = c' := h.lift_snd _ _ _
        refine ⟨degreewiseEquiv j P n (Sum.inr ⟨⟨s, l⟩, d, hd⟩), ?_, ?_⟩
        · rw [degreewiseEquiv_naturality]
          change degreewiseEquiv j X n (Sum.inr ⟨⟨s, l ≫ a⟩, d, hd⟩) = _
          rw [hlX]
        · rw [degreewiseEquiv_naturality]
          change degreewiseEquiv j V n (Sum.inr ⟨⟨s, l ≫ b⟩, d, hd⟩) = _
          rw [hlV]

private lemma mappedPullback {P X V Y : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ V} {f : X ⟶ Y} {g : V ⟶ Y}
    (h : IsPullback a b f g) :
    IsPullback ((labelledFreeFiller j).map a) ((labelledFreeFiller j).map b)
      ((labelledFreeFiller j).map f) ((labelledFreeFiller j).map g) := by
  have w : (labelledFreeFiller j).map a ≫ (labelledFreeFiller j).map f =
      (labelledFreeFiller j).map b ≫ (labelledFreeFiller j).map g := by
    rw [← Functor.map_comp, ← Functor.map_comp, h.w]
  refine ⟨⟨w⟩, ⟨?_⟩⟩
  apply evaluationJointlyReflectsLimits _
  rintro ⟨⟨n⟩⟩
  exact (isLimitMapConePullbackConeEquiv ((evaluation _ _).obj (op ⦋n⦌)) w).symm
    (mappedPullback_obj j h n).isLimit

/-- The actual all-labelled attachment functor preserves every pullback,
including spans whose maps are not monomorphisms. -/
instance preservesPullbacks : PreservesLimitsOfShape WalkingCospan (labelledFreeFiller j) := by
  apply preservesLimitsOfShape_walkingCospan_of_forall_isPullback
  intro X V Y f g _
  exact ⟨pullback f g, pullback.fst f g, pullback.snd f g,
    IsPullback.of_hasPullback f g, mappedPullback j (IsPullback.of_hasPullback f g)⟩

end SSet.labelledFreeFiller
