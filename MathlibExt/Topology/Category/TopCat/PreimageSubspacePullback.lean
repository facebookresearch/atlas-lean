/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.Subspace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Preimage subspaces and pullback squares

For a continuous map `f : X → Y` and a subset `U ⊆ Y`, the subspace
`f⁻¹(U)` is the pullback of the inclusion `U → Y` along `f`. Its maps
are restriction to `U` and the inclusion into `X`. A commuting square
can itself be restricted to the corresponding preimage subspaces, with
the same continuous map between the ambient total spaces. All spaces
here lie in the given universe `u`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace TopCat

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (U : Set Y)

/-- For topological spaces `X`, `Y` in universe `u`, a continuous map
`f : X → Y` and any subset `U ⊆ Y`, the square with top map
`f⁻¹(U) → U`, left and right subspace inclusions, and bottom map `f`
is a categorical pullback in `TopCat`. -/
theorem isPullback_preimageSubspace :
    IsPullback (subspaceMap f (fun _x hx => hx : Set.MapsTo f (f ⁻¹' U) U))
      (subspaceIncl (f ⁻¹' U)) (subspaceIncl U) f := by
  apply IsPullback.of_isLimit
    (c := PullbackCone.mk
      (subspaceMap f (fun x hx => hx : Set.MapsTo f (f ⁻¹' U) U))
      (subspaceIncl (f ⁻¹' U))
      (subspaceMap_comp_subspaceIncl f (fun x hx => hx)))
  apply PullbackCone.IsLimit.mk (subspaceMap_comp_subspaceIncl f (fun x hx => hx))
  case lift =>
    intro s
    have hmem : ∀ w : s.pt, f (s.snd w) ∈ U := fun w => by
      have h : ((s.fst ≫ subspaceIncl (U : Set Y))) w = ((s.snd ≫ f)) w :=
        ConcreteCategory.congr_hom s.condition w
      have h_eq : (subspaceIncl (U : Set Y)) (s.fst w) = f (s.snd w) := h
      exact h_eq ▸ (s.fst w).2
    exact (TopCat.ofHom
      ⟨(fun w : s.pt => (⟨s.snd w, hmem w⟩ : ↥(TopCat.of (f ⁻¹' U)))),
        Continuous.subtype_mk s.snd.hom.continuous hmem⟩ :
      s.pt ⟶ TopCat.of (f ⁻¹' U))
  case fac_left =>
    intro s
    apply TopCat.hom_ext
    ext w
    have h : ((s.fst ≫ subspaceIncl (U : Set Y))) w = ((s.snd ≫ f)) w :=
      ConcreteCategory.congr_hom s.condition w
    have h_eq : (subspaceIncl (U : Set Y)) (s.fst w) = f (s.snd w) := h
    exact h_eq.symm
  case fac_right =>
    intro s
    apply TopCat.hom_ext
    ext w
    rfl
  case uniq =>
    intro s m _ h₂
    apply TopCat.hom_ext
    ext w
    have h2w : ((m ≫ subspaceIncl (f ⁻¹' U))) w = (s.snd) w :=
      ConcreteCategory.congr_hom h₂ w
    exact h2w

/-- Let `E₁ → E`, `E₁ → B₁`, `E → B` and `B₁ → B` form a commuting
square of topological spaces in universe `u`. If `U ⊆ B` and `U₁ ⊆ B₁`
satisfy `b₁⁻¹(U) = U₁`, the induced map from `p₁⁻¹(U₁)` to `p⁻¹(U)`,
together with the two subspace inclusions and the original map `E₁ → E`,
again forms a pullback square. -/
theorem isPullback_preimageSubspace_of_comm
    {E E₁ B B₁ : TopCat.{u}}
    {p : E ⟶ B} {p₁ : E₁ ⟶ B₁} {e₁ : E₁ ⟶ E} {b₁ : B₁ ⟶ B}
    (w : e₁ ≫ p = p₁ ≫ b₁)
    (U : Set B) (U₁ : Set B₁) (hU : ⇑b₁ ⁻¹' U = U₁) :
    IsPullback
      (TopCat.subspaceMap e₁ (by
        intro x hx
        simp only [Set.mem_preimage] at hx ⊢
        have hwb : p (e₁ x) = b₁ (p₁ x) := by
          have h := ConcreteCategory.congr_hom w x
          simpa using h
        have hxU : b₁ (p₁ x) ∈ U := by
          rw [←Set.mem_preimage, hU]
          exact hx
        rw [hwb]
        exact hxU : Set.MapsTo e₁ (⇑p₁ ⁻¹' U₁) (⇑p ⁻¹' U)))
      (TopCat.subspaceIncl (⇑p₁ ⁻¹' U₁))
      (TopCat.subspaceIncl (⇑p ⁻¹' U)) e₁ := by
  have hPre : ⇑e₁ ⁻¹' (⇑p ⁻¹' U) = ⇑p₁ ⁻¹' U₁ := by
    ext x
    have hw : p (e₁ x) = b₁ (p₁ x) := ConcreteCategory.congr_hom w x
    change p (e₁ x) ∈ U ↔ p₁ x ∈ U₁
    rw [hw, ← hU]
    rfl
  let eP : TopCat.of (⇑e₁ ⁻¹' (⇑p ⁻¹' U)) ≅ TopCat.of (⇑p₁ ⁻¹' U₁) :=
    TopCat.isoOfHomeo (Homeomorph.setCongr hPre)
  exact (TopCat.isPullback_preimageSubspace e₁ (⇑p ⁻¹' U)).of_iso
    eP (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (commfst := by apply TopCat.hom_ext; ext x; rfl)
    (commsnd := by apply TopCat.hom_ext; ext x; rfl)
    (commf := by rfl) (commg := by rfl)

end TopCat
