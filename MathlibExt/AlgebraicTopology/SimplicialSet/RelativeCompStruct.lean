/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import MathlibExt.AlgebraicTopology.SimplicialSet.CompStructCompat

/-!
# Original relative composition and association triangles

The native inner-fibration lifts of the original two- and three-horns
retain every supplied edge and triangle. The whole prescribed base simplex
is retained, so the missing composition and association faces have their
specified full base images. No quasicategory or equivalence certificate is
needed to fill these relative inner horns.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Edge.CompStruct

/-- Lift a composition over the entire specified original base triangle. -/
theorem exists_over {X B : SSet.{u}} (p : X ⟶ B) [InnerFibration p]
    {x₀ x₁ x₂ : X _⦋0⦌} (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂)
    (b₀₂ : Edge (p.app _ x₀) (p.app _ x₂))
    (S : CompStruct (e₀₁.map p) (e₁₂.map p) b₀₂) :
    ∃ (e₀₂ : Edge x₀ x₂) (H : CompStruct e₀₁ e₁₂ e₀₂),
      p.app (Opposite.op ⦋2⦌) H.simplex = S.simplex ∧ (e₀₂.map p).edge = b₀₂.edge := by
  have glue : stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm e₀₁.edge =
      stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm e₁₂.edge :=
    e₀₁.δ_zero_yonedaEquiv_symm.trans e₁₂.δ_one_yonedaEquiv_symm.symm
  obtain ⟨σ₀, h₂, h₀⟩ := horn₂₁.isPushout.exists_desc
    (yonedaEquiv.symm e₀₁.edge) (yonedaEquiv.symm e₁₂.edge) glue
  have h₂' : horn.ι (1 : Fin 3) (2 : Fin 3) (by decide) ≫ σ₀ = yonedaEquiv.symm e₀₁.edge := h₂
  have h₀' : horn.ι (1 : Fin 3) (0 : Fin 3) (by decide) ≫ σ₀ = yonedaEquiv.symm e₁₂.edge := h₀
  have hi₂ : horn₂₁.ι₀₁.{u} ≫ (horn 2 (1 : Fin 3)).ι = stdSimplex.δ (2 : Fin 3) :=
    horn.ι_ι 1 (2 : Fin 3) (by decide)
  have hi₀ : horn₂₁.ι₁₂.{u} ≫ (horn 2 (1 : Fin 3)).ι = stdSimplex.δ (0 : Fin 3) :=
    horn.ι_ι 1 (0 : Fin 3) (by decide)
  let b : (Δ[2] : SSet.{u}) ⟶ B := yonedaEquiv.symm S.simplex
  have hsq : σ₀ ≫ p = (horn 2 (1 : Fin 3)).ι ≫ b := by
    apply horn₂₁.isPushout.hom_ext
    · rw [← Category.assoc, h₂, ← Category.assoc, hi₂, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg yonedaEquiv.symm S.d₂.symm
    · rw [← Category.assoc, h₀, ← Category.assoc, hi₀, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg yonedaEquiv.symm S.d₀.symm
  let _ : HasLiftingProperty (horn 2 (1 : Fin 3)).ι p := InnerFibration.mem _
    (horn_ι_mem_innerHornInclusions (n := 2) (i := (1 : Fin 3)) (by decide) (by decide))
  let sq : CommSq σ₀ (horn 2 (1 : Fin 3)).ι p b := ⟨hsq⟩
  let T := sq.lift
  have hT : (horn 2 (1 : Fin 3)).ι ≫ T = σ₀ := sq.fac_left
  have hd₂ : X.δ (2 : Fin 3) (yonedaEquiv T) = e₀₁.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (1 : Fin 3) (2 : Fin 3) (by decide),
      hT, h₂', Equiv.apply_symm_apply]
  have hd₀ : X.δ (0 : Fin 3) (yonedaEquiv T) = e₁₂.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (1 : Fin 3) (0 : Fin 3) (by decide),
      hT, h₀', Equiv.apply_symm_apply]
  obtain ⟨a₀, a₁, a₂, f₀₁, f₁₂, e₀₂, H, hH⟩ := Edge.CompStruct.exists_of_simplex (yonedaEquiv T)
  have he₀₁ : f₀₁.edge = e₀₁.edge := H.d₂.symm.trans ((congrArg (X.δ (2 : Fin 3)) hH).trans hd₂)
  have he₁₂ : f₁₂.edge = e₁₂.edge := H.d₀.symm.trans ((congrArg (X.δ (0 : Fin 3)) hH).trans hd₀)
  have ha₀ : a₀ = x₀ := by rw [← f₀₁.src_eq, he₀₁, e₀₁.src_eq]
  have ha₁ : a₁ = x₁ := by rw [← f₀₁.tgt_eq, he₀₁, e₀₁.tgt_eq]
  have ha₂ : a₂ = x₂ := by rw [← f₁₂.tgt_eq, he₁₂, e₁₂.tgt_eq]
  subst a₀
  subst a₁
  subst a₂
  have hf₀₁ : f₀₁ = e₀₁ := Edge.ext he₀₁
  have hf₁₂ : f₁₂ = e₁₂ := Edge.ext he₁₂
  subst f₀₁
  subst f₁₂
  have hb : p.app (Opposite.op ⦋2⦌) H.simplex = S.simplex := by
    rw [hH, ← yonedaEquiv_comp, sq.fac_right]
    exact Equiv.apply_symm_apply yonedaEquiv _
  refine ⟨e₀₂, H, hb, ?_⟩
  rw [Edge.map_edge, ← H.d₁, SSet.δ_naturality_apply, hb]
  exact S.d₁

/-- The original missing association face of a relative inner three-horn retains its base face. -/
theorem exists_assoc_left_over {X B : SSet.{u}} (p : X ⟶ B) [InnerFibration p]
    {x₀ x₁ x₂ x₃ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (H₃ : CompStruct e₀₁ e₁₂ e₀₂) (H₀ : CompStruct e₁₂ e₂₃ e₁₃)
    (H₂ : CompStruct e₀₁ e₁₃ e₀₃) (b : B _⦋3⦌)
    (hb₀ : p.app (Opposite.op ⦋2⦌) H₀.simplex = B.δ 0 b)
    (hb₂ : p.app (Opposite.op ⦋2⦌) H₂.simplex = B.δ 2 b)
    (hb₃ : p.app (Opposite.op ⦋2⦌) H₃.simplex = B.δ 3 b) :
    ∃ H₁ : CompStruct e₀₂ e₂₃ e₀₃, p.app (Opposite.op ⦋2⦌) H₁.simplex = B.δ 1 b := by
  obtain ⟨σ₀, h₀, h₂, h₃⟩ := horn₃₁.exists_desc (yonedaEquiv.symm H₀.simplex)
    (yonedaEquiv.symm H₂.simplex) (yonedaEquiv.symm H₃.simplex) (by simp) (by simp) (by simp)
  have h₀' : horn.ι (1 : Fin 4) (0 : Fin 4) (by decide) ≫ σ₀ = yonedaEquiv.symm H₀.simplex := h₀
  have h₂' : horn.ι (1 : Fin 4) (2 : Fin 4) (by decide) ≫ σ₀ = yonedaEquiv.symm H₂.simplex := h₂
  have h₃' : horn.ι (1 : Fin 4) (3 : Fin 4) (by decide) ≫ σ₀ = yonedaEquiv.symm H₃.simplex := h₃
  have hsq : σ₀ ≫ p = (horn 3 (1 : Fin 4)).ι ≫ yonedaEquiv.symm b := by
    apply horn.hom_ext'
    intro j hj
    have hjv : j.val ≠ 1 := fun h => hj (Fin.ext h)
    have hcases : j.val = 0 ∨ j.val = 2 ∨ j.val = 3 := by omega
    rcases hcases with h0 | h2 | h3
    · have hj' : j = 0 := Fin.ext h0
      subst j
      rw [← Category.assoc, h₀', horn.ι_ι_assoc, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm, hb₀]
    · have hj' : j = 2 := Fin.ext h2
      subst j
      rw [← Category.assoc, h₂', horn.ι_ι_assoc, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm, hb₂]
    · have hj' : j = 3 := Fin.ext h3
      subst j
      rw [← Category.assoc, h₃', horn.ι_ι_assoc, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm, hb₃]
  let _ : HasLiftingProperty (horn 3 (1 : Fin 4)).ι p := InnerFibration.mem _
    (horn_ι_mem_innerHornInclusions (n := 3) (i := (1 : Fin 4)) (by decide) (by decide))
  let sq : CommSq σ₀ (horn 3 (1 : Fin 4)).ι p (yonedaEquiv.symm b) := ⟨hsq⟩
  let T := sq.lift
  have hT : (horn 3 (1 : Fin 4)).ι ≫ T = σ₀ := sq.fac_left
  have hd₀ : X.δ (0 : Fin 4) (yonedaEquiv T) = H₀.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (1 : Fin 4) (0 : Fin 4) (by decide),
      hT, h₀', Equiv.apply_symm_apply]
  have hd₂ : X.δ (2 : Fin 4) (yonedaEquiv T) = H₂.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (1 : Fin 4) (2 : Fin 4) (by decide),
      hT, h₂', Equiv.apply_symm_apply]
  have hd₃ : X.δ (3 : Fin 4) (yonedaEquiv T) = H₃.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (1 : Fin 4) (3 : Fin 4) (by decide),
      hT, h₃', Equiv.apply_symm_apply]
  have face₂ : X.δ (2 : Fin 3) (X.δ (1 : Fin 4) (yonedaEquiv T)) = e₀₂.edge := by
    have hi := δ_comp_δ''_apply (S := X) (i := (1 : Fin 4)) (j := (2 : Fin 3))
      (by decide) (yonedaEquiv T)
    change X.δ 1 (X.δ 3 (yonedaEquiv T)) = X.δ 2 (X.δ 1 (yonedaEquiv T)) at hi
    rw [← hi, hd₃, H₃.d₁]
  have face₀ : X.δ (0 : Fin 3) (X.δ (1 : Fin 4) (yonedaEquiv T)) = e₂₃.edge := by
    have hi := δ_comp_δ_self_apply (S := X) (i := (0 : Fin 3)) (yonedaEquiv T)
    change X.δ 0 (X.δ 0 (yonedaEquiv T)) = X.δ 0 (X.δ 1 (yonedaEquiv T)) at hi
    rw [← hi, hd₀, H₀.d₀]
  have face₁ : X.δ (1 : Fin 3) (X.δ (1 : Fin 4) (yonedaEquiv T)) = e₀₃.edge := by
    have hi := δ_comp_δ_self_apply (S := X) (i := (1 : Fin 3)) (yonedaEquiv T)
    change X.δ 1 (X.δ 1 (yonedaEquiv T)) = X.δ 1 (X.δ 2 (yonedaEquiv T)) at hi
    rw [hi, hd₂, H₂.d₁]
  let H₁ := CompStruct.mk (X.δ (1 : Fin 4) (yonedaEquiv T)) face₂ face₀ face₁
  refine ⟨H₁, ?_⟩
  have hp : p.app (Opposite.op ⦋3⦌) (yonedaEquiv T) = b := by
    rw [← yonedaEquiv_comp, sq.fac_right]
    exact Equiv.apply_symm_apply yonedaEquiv _
  change p.app _ (X.δ 1 (yonedaEquiv T)) = B.δ 1 b
  rw [SSet.δ_naturality_apply, hp]

/-- The original missing association face of a relative inner three-horn retains its base face. -/
theorem exists_assoc_right_over {X B : SSet.{u}} (p : X ⟶ B) [InnerFibration p]
    {x₀ x₁ x₂ x₃ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (H₃ : CompStruct e₀₁ e₁₂ e₀₂) (H₀ : CompStruct e₁₂ e₂₃ e₁₃)
    (H₁ : CompStruct e₀₂ e₂₃ e₀₃) (b : B _⦋3⦌)
    (hb₀ : p.app (Opposite.op ⦋2⦌) H₀.simplex = B.δ 0 b)
    (hb₁ : p.app (Opposite.op ⦋2⦌) H₁.simplex = B.δ 1 b)
    (hb₃ : p.app (Opposite.op ⦋2⦌) H₃.simplex = B.δ 3 b) :
    ∃ H₂ : CompStruct e₀₁ e₁₃ e₀₃, p.app (Opposite.op ⦋2⦌) H₂.simplex = B.δ 2 b := by
  obtain ⟨σ₀, h₀, h₁, h₃⟩ := horn₃₂.exists_desc (yonedaEquiv.symm H₀.simplex)
    (yonedaEquiv.symm H₁.simplex) (yonedaEquiv.symm H₃.simplex) (by simp) (by simp) (by simp)
  have h₀' : horn.ι (2 : Fin 4) (0 : Fin 4) (by decide) ≫ σ₀ = yonedaEquiv.symm H₀.simplex := h₀
  have h₁' : horn.ι (2 : Fin 4) (1 : Fin 4) (by decide) ≫ σ₀ = yonedaEquiv.symm H₁.simplex := h₁
  have h₃' : horn.ι (2 : Fin 4) (3 : Fin 4) (by decide) ≫ σ₀ = yonedaEquiv.symm H₃.simplex := h₃
  have hsq : σ₀ ≫ p = (horn 3 (2 : Fin 4)).ι ≫ yonedaEquiv.symm b := by
    apply horn.hom_ext'
    intro j hj
    have hjv : j.val ≠ 2 := fun h => hj (Fin.ext h)
    have hcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 3 := by omega
    rcases hcases with h0 | h1 | h3
    · have hj' : j = 0 := Fin.ext h0
      subst j
      rw [← Category.assoc, h₀', horn.ι_ι_assoc, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm, hb₀]
    · have hj' : j = 1 := Fin.ext h1
      subst j
      rw [← Category.assoc, h₁', horn.ι_ι_assoc, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm, hb₁]
    · have hj' : j = 3 := Fin.ext h3
      subst j
      rw [← Category.assoc, h₃', horn.ι_ι_assoc, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm, hb₃]
  let _ : HasLiftingProperty (horn 3 (2 : Fin 4)).ι p := InnerFibration.mem _
    (horn_ι_mem_innerHornInclusions (n := 3) (i := (2 : Fin 4)) (by decide) (by decide))
  let sq : CommSq σ₀ (horn 3 (2 : Fin 4)).ι p (yonedaEquiv.symm b) := ⟨hsq⟩
  let T := sq.lift
  have hT : (horn 3 (2 : Fin 4)).ι ≫ T = σ₀ := sq.fac_left
  have hd₀ : X.δ (0 : Fin 4) (yonedaEquiv T) = H₀.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (2 : Fin 4) (0 : Fin 4) (by decide),
      hT, h₀', Equiv.apply_symm_apply]
  have hd₁ : X.δ (1 : Fin 4) (yonedaEquiv T) = H₁.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (2 : Fin 4) (1 : Fin 4) (by decide),
      hT, h₁', Equiv.apply_symm_apply]
  have hd₃ : X.δ (3 : Fin 4) (yonedaEquiv T) = H₃.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (2 : Fin 4) (3 : Fin 4) (by decide),
      hT, h₃', Equiv.apply_symm_apply]
  have face₂ : X.δ (2 : Fin 3) (X.δ (2 : Fin 4) (yonedaEquiv T)) = e₀₁.edge := by
    have hi := δ_comp_δ_self_apply (S := X) (i := (2 : Fin 3)) (yonedaEquiv T)
    change X.δ 2 (X.δ 2 (yonedaEquiv T)) = X.δ 2 (X.δ 3 (yonedaEquiv T)) at hi
    rw [hi, hd₃, H₃.d₂]
  have face₀ : X.δ (0 : Fin 3) (X.δ (2 : Fin 4) (yonedaEquiv T)) = e₁₃.edge := by
    have hi := δ_comp_δ''_apply (S := X) (i := (0 : Fin 4)) (j := (1 : Fin 3))
      (by decide) (yonedaEquiv T)
    change X.δ 0 (X.δ 2 (yonedaEquiv T)) = X.δ 1 (X.δ 0 (yonedaEquiv T)) at hi
    rw [hi, hd₀, H₀.d₁]
  have face₁ : X.δ (1 : Fin 3) (X.δ (2 : Fin 4) (yonedaEquiv T)) = e₀₃.edge := by
    have hi := δ_comp_δ_self_apply (S := X) (i := (1 : Fin 3)) (yonedaEquiv T)
    change X.δ 1 (X.δ 1 (yonedaEquiv T)) = X.δ 1 (X.δ 2 (yonedaEquiv T)) at hi
    rw [← hi, hd₁, H₁.d₁]
  let H₂ := CompStruct.mk (X.δ (2 : Fin 4) (yonedaEquiv T)) face₂ face₀ face₁
  refine ⟨H₂, ?_⟩
  have hp : p.app (Opposite.op ⦋3⦌) (yonedaEquiv T) = b := by
    rw [← yonedaEquiv_comp, sq.fac_right]
    exact Equiv.apply_symm_apply yonedaEquiv _
  change p.app _ (X.δ 2 (yonedaEquiv T)) = B.δ 2 b
  rw [SSet.δ_naturality_apply, hp]

end SSet.Edge.CompStruct
