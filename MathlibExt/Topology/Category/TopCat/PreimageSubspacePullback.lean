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
are restriction to `U` and the inclusion into `X`. A pullback square
can itself be restricted to the corresponding preimage subspaces, with
the same continuous map between the ambient total spaces. All spaces
here lie in the given universe `u`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicTopology

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

/-- Let `E₁ → E`, `E₁ → B₁`, `E → B` and `B₁ → B` form a pullback
square of topological spaces in universe `u`. If `U ⊆ B` and `U₁ ⊆ B₁`
satisfy `b₁⁻¹(U) = U₁`, the induced map from `p₁⁻¹(U₁)` to `p⁻¹(U)`,
together with the two subspace inclusions and the original map `E₁ → E`,
again forms a pullback square. -/
theorem isPullback_preimageSubspace_of_isPullback
    {E E₁ B B₁ : TopCat.{u}}
    {p : E ⟶ B} {p₁ : E₁ ⟶ B₁} {e₁ : E₁ ⟶ E} {b₁ : B₁ ⟶ B}
    (sq : IsPullback e₁ p₁ p b₁)
    (U : Set B) (U₁ : Set B₁) (hU : ⇑b₁ ⁻¹' U = U₁) :
    IsPullback
      (AlgebraicTopology.subspaceMap e₁ (by
        intro x hx
        simp only [Set.mem_preimage] at hx ⊢
        have hwb : p (e₁ x) = b₁ (p₁ x) := by
          have h := ConcreteCategory.congr_hom sq.w x
          simpa using h
        have hxU : b₁ (p₁ x) ∈ U := by
          rw [←Set.mem_preimage, hU]
          exact hx
        rw [hwb]
        exact hxU : Set.MapsTo e₁ (⇑p₁ ⁻¹' U₁) (⇑p ⁻¹' U)))
      (AlgebraicTopology.subspaceIncl (⇑p₁ ⁻¹' U₁))
      (AlgebraicTopology.subspaceIncl (⇑p ⁻¹' U)) e₁ := by
  have hPre : ⇑p₁ ⁻¹' (⇑b₁ ⁻¹' U) = ⇑p₁ ⁻¹' U₁ := by rw [hU]
  have hMaps_e : Set.MapsTo e₁ (⇑p₁ ⁻¹' (⇑b₁ ⁻¹' U)) (⇑p ⁻¹' U) := by
    intro x hx
    simp only [Set.mem_preimage] at hx ⊢
    have hwb : p (e₁ x) = b₁ (p₁ x) := by
      have h := ConcreteCategory.congr_hom sq.w x
      simpa using h
    rw [hwb]
    exact hx
  have h_p1 :=
    AlgebraicTopology.isPullback_preimageSubspace p₁ (⇑b₁ ⁻¹' U)
  have h_b1 := AlgebraicTopology.isPullback_preimageSubspace b₁ U
  have hRight := AlgebraicTopology.isPullback_preimageSubspace p U
  have hOuter0 := h_p1.paste_horiz h_b1
  have hTopEq :
      AlgebraicTopology.subspaceMap p₁
          (show Set.MapsTo p₁ (⇑p₁ ⁻¹' (⇑b₁ ⁻¹' U)) (⇑b₁ ⁻¹' U) from fun _ hx => hx) ≫
        AlgebraicTopology.subspaceMap b₁
          (show Set.MapsTo b₁ (⇑b₁ ⁻¹' U) U from fun _ hx => hx) =
      AlgebraicTopology.subspaceMap e₁ hMaps_e ≫
        AlgebraicTopology.subspaceMap p
          (show Set.MapsTo p (⇑p ⁻¹' U) U from fun _ hx => hx) := by
    apply TopCat.hom_ext
    ext x
    change b₁ (p₁ x.1) = p (e₁ x.1)
    have h := ConcreteCategory.congr_hom sq.w x.1
    simpa using h.symm
  have hBotEq : p₁ ≫ b₁ = e₁ ≫ p := sq.w.symm
  rw [hTopEq, hBotEq] at hOuter0
  have hComm :
      AlgebraicTopology.subspaceMap e₁ hMaps_e ≫
          AlgebraicTopology.subspaceIncl (⇑p ⁻¹' U) =
        AlgebraicTopology.subspaceIncl (⇑p₁ ⁻¹' (⇑b₁ ⁻¹' U)) ≫ e₁ :=
    AlgebraicTopology.subspaceMap_comp_subspaceIncl e₁ hMaps_e
  have hFinalPre := IsPullback.of_right hOuter0 hComm hRight
  let eP : TopCat.of (⇑p₁ ⁻¹' (⇑b₁ ⁻¹' U)) ≅ TopCat.of (⇑p₁ ⁻¹' U₁) := {
    hom := AlgebraicTopology.subspaceInclOfSubset (by rw [hPre])
    inv := AlgebraicTopology.subspaceInclOfSubset (by rw [←hPre])
    hom_inv_id := by apply TopCat.hom_ext; ext x; rfl
    inv_hom_id := by apply TopCat.hom_ext; ext x; rfl }
  exact hFinalPre.of_iso eP (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (commfst := by
      apply TopCat.hom_ext
      ext x
      simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply, Iso.refl_hom,
        AlgebraicTopology.subspaceMap, TopCat.hom_ofHom]
      have hE : ((ConcreteCategory.hom eP.hom) x).1 = x.1 := by
        rw [show eP.hom = AlgebraicTopology.subspaceInclOfSubset (by rw [hPre]) from rfl]
        rfl
      exact congrArg ⇑e₁ hE.symm)
    (commsnd := by
      apply TopCat.hom_ext
      ext x
      simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply, Iso.refl_hom,
        AlgebraicTopology.subspaceIncl, TopCat.hom_ofHom]
      have hE : ((ConcreteCategory.hom eP.hom) x).1 = x.1 := by
        rw [show eP.hom = AlgebraicTopology.subspaceInclOfSubset (by rw [hPre]) from rfl]
        rfl
      exact hE.symm)
    (commf := by rfl)
    (commg := by rfl)

end AlgebraicTopology
