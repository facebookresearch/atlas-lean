/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
ported from `TauCeti/AlgebraicGeometry/Morphisms/Epi.lean` in TauCetiProject/TauCeti at
revision 62bbc0596dc3539d488232e4e924a338548ea0a9. Retain the complete stalk-injective
epimorphism, open base-change and morphism-glueing dependencies; omit unrelated
locally-ringed-space section descent. No unresolved result is added.
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y Z : Scheme.{u}}

/-- **A surjective morphism of schemes with injective stalk maps is an epimorphism.** -/
theorem epi_of_surjective_of_stalkMap_injective (f : X ⟶ Y) [Surjective f]
    (h : ∀ x, Function.Injective (f.stalkMap x)) : Epi f := by
  apply Functor.epi_of_epi_map Scheme.forgetToLocallyRingedSpace
  apply Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  refine SheafedSpace.epi_of_base_surjective_of_stalk_mono _ ‹Surjective f›.surj fun x ↦ ?_
  exact ConcreteCategory.mono_of_injective _ (h x)

/-- The stalk maps of the base change of `f` along an open immersion are injective when those of
`f` are. -/
theorem stalkMap_pullback_snd_injective (f : X ⟶ Y) (g : Z ⟶ Y) [IsOpenImmersion g]
    (h : ∀ x, Function.Injective (f.stalkMap x)) (z : ↥(pullback f g)) :
    Function.Injective ((pullback.snd f g).stalkMap z) := by
  -- The stalk map of `pullback.fst ≫ f` is injective, since `pullback.fst` is an open immersion.
  have hfst : Mono ((pullback.fst f g ≫ f).stalkMap z) := by
    rw [stalkMap_comp]
    exact mono_comp' (ConcreteCategory.mono_of_injective _ (h _)) inferInstance
  -- It is the stalk map of `pullback.snd ≫ g`, which first applies the bijective stalk map of `g`.
  have hsnd : Mono (g.stalkMap (pullback.snd f g z) ≫ (pullback.snd f g).stalkMap z) := by
    rw [← stalkMap_comp, stalkMap_congr_hom _ _ pullback.condition.symm]
    exact (mono_comp_iff_of_isIso (Y.presheaf.stalkCongr _).hom _).mpr hfst
  rw [mono_comp_iff_of_isIso] at hsnd
  exact ConcreteCategory.injective_of_mono_of_preservesPullback _

/-- The base change of a surjective morphism with injective stalk maps along an open immersion is
an epimorphism. -/
theorem epi_pullback_snd_of_isOpenImmersion (f : X ⟶ Y) [Surjective f] (g : Z ⟶ Y)
    [IsOpenImmersion g] (h : ∀ x, Function.Injective (f.stalkMap x)) :
    Epi (pullback.snd f g) :=
  epi_of_surjective_of_stalkMap_injective _ (stalkMap_pullback_snd_injective f g h)

/-- **Descent along a morphism which stays an epimorphism over open subschemes.** Let `π : X ⟶ Y`
be a morphism whose base change along every open immersion is an epimorphism, and let `f : X ⟶ Z`.
If over each member `U_i` of an open cover of `Y` the base change of `f` factors through
`X ×_Y U_i ⟶ U_i`, then `f` factors through `π`. The local factorizations agree on overlaps
because the base change of `π` to an overlap is an epimorphism, so they glue. -/
theorem exists_comp_eq_of_openCover (π : X ⟶ Y)
    (hπ : ∀ ⦃U : Scheme.{u}⦄ (g : U ⟶ Y), IsOpenImmersion g → Epi (pullback.snd π g))
    (𝒰 : Y.OpenCover) (f : X ⟶ Z) (u : ∀ i, 𝒰.X i ⟶ Z)
    (hu : ∀ i, pullback.fst π (𝒰.f i) ≫ f = pullback.snd π (𝒰.f i) ≫ u i) :
    ∃ h : Y ⟶ Z, π ≫ h = f := by
  refine ⟨𝒰.glueMorphisms u fun i k ↦ ?_, ?_⟩
  · -- Over the overlap `V = U_i ×_Y U_k`, both restrictions agree with `f` on `X ×_Y V`.
    have := hπ (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) inferInstance
    have key (j : 𝒰.I₀) (p : pullback (𝒰.f i) (𝒰.f k) ⟶ 𝒰.X j)
        (hp : p ≫ 𝒰.f j = pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) :
        pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) ≫ p ≫ u j =
          pullback.fst π (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) ≫ f := by
      have w : pullback.fst π (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) ≫ π =
          (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) ≫ p) ≫ 𝒰.f j := by
        rw [Category.assoc, hp]
        exact pullback.condition
      rw [← Category.assoc, ← pullback.lift_snd _ _ w, Category.assoc, ← hu j,
        pullback.lift_fst_assoc]
    rw [← cancel_epi (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i)), key i _ rfl,
      key k _ pullback.condition.symm]
  · refine Cover.hom_ext (𝒰.pullback₁ π) _ _ fun (i : 𝒰.I₀) ↦ ?_
    -- The components of the pulled-back cover are `pullback.fst` by definition
    -- (`PreZeroHypercover.pullback₁_f`); that `simps` lemma does not fire through `Scheme.Cover.f`.
    calc _ = pullback.fst π (𝒰.f i) ≫ π ≫ 𝒰.glueMorphisms u _ := rfl
      _ = pullback.fst π (𝒰.f i) ≫ f := by
        rw [pullback.condition_assoc, Cover.ι_glueMorphisms, hu i]

end AlgebraicGeometry.Scheme.Hom
