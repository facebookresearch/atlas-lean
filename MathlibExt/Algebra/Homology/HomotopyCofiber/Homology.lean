/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology of the composite with a cofiber inclusion

Let C be a preadditive category, c a complex shape with decidable differential
relation, and φ:F → G a map whose homotopy cofiber exists. The target
inclusion u:G → Cofib(φ) is monic, with a retraction in every degree.

If c.Rel(i,j), the shifted-source inclusion v:Fⱼ → Cofib(φ)ᵢ
makes the image of every degree-j cycle under uⱼ∘φⱼ a boundary:
uⱼ ∘ φⱼ ∘ i_Z = d_Cofib(i,j) ∘ v ∘ i_Z.
Consequently Hⱼ(u∘φ)=0 when F and Cofib(φ) have the chosen homology
objects at j. Only a predecessor of this degree is needed; the category
and complex-index universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {F G : HomologicalComplex C c} (φ : F ⟶ G) [HasHomotopyCofiber φ]

/-- In a preadditive category C, for a complex shape c with decidable
differential relation and a map φ:F → G whose homotopy cofiber exists,
the target inclusion G → Cofib(φ) is a monomorphism. Its component
in every degree is split monic with the target-coordinate projection
as retraction. -/
theorem mono_inr : Mono (inr φ) := by
  apply HomologicalComplex.mono_of_mono_f
  intro j
  exact (show SplitMono ((inr φ).f j) from
    { retraction := sndX φ j
      id := inrX_sndX φ j }).mono

/-- Let C be preadditive, c a complex shape with decidable differential
relation, and φ:F → G have a homotopy cofiber. For c.Rel(i,j),
assume F has its chosen homology object at j. Write
i_Z:Zⱼ(F) → Fⱼ, uⱼ:Gⱼ → Cofib(φ)ⱼ and
v:Fⱼ → Cofib(φ)ᵢ for the cycle and cofiber inclusions. Then
uⱼ ∘ φⱼ ∘ i_Z = d_Cofib(i,j) ∘ v ∘ i_Z:
the composite takes cycles to boundaries. -/
theorem cycles_comp_inr_eq_boundary (i j : ι) (hij : c.Rel i j) [F.HasHomology j] :
    F.iCycles j ≫ φ.f j ≫ inrX φ j =
      F.iCycles j ≫ inlX φ j i hij ≫ (homotopyCofiber φ).d i j := by
  by_cases hj : c.Rel j (c.next j)
  · have hd : inlX φ j i hij ≫ (homotopyCofiber φ).d i j =
        -F.d j (c.next j) ≫ inlX φ (c.next j) j hj + φ.f j ≫ inrX φ j :=
      inlX_d φ i j (c.next j) hij hj
    have hz : F.iCycles j ≫ (-(F.d j (c.next j) ≫ inlX φ (c.next j) j hj)) = 0 := by
      rw [Preadditive.comp_neg, F.iCycles_d_assoc, zero_comp, neg_zero]
    calc
      _ = F.iCycles j ≫
          (-F.d j (c.next j) ≫ inlX φ (c.next j) j hj + φ.f j ≫ inrX φ j) := by
        rw [Preadditive.comp_add, hz, zero_add]
      _ = F.iCycles j ≫ (inlX φ j i hij ≫ (homotopyCofiber φ).d i j) :=
        congrArg (fun a => F.iCycles j ≫ a) hd.symm
      _ = _ := rfl
  · exact (congrArg (fun a => F.iCycles j ≫ a) (inlX_d' φ i j hij hj)).symm

/-- Let C be preadditive, c a complex shape with decidable differential
relation, and φ:F → G have a homotopy cofiber. If c.Rel(i,j) and
F and Cofib(φ) have their chosen homology objects at j, then the
composite F → G → Cofib(φ) induces the zero homology map in degree j. -/
theorem homologyMap_comp_inr_eq_zero (i j : ι) (hij : c.Rel i j)
    [F.HasHomology j] [(homotopyCofiber φ).HasHomology j] :
    homologyMap (φ ≫ inr φ) j = 0 := by
  let K := homotopyCofiber φ
  let S : ShortComplex C := F.sc j
  let T : ShortComplex C := K.sc j
  let ψ : S ⟶ T := (shortComplexFunctor C c j).map (φ ≫ inr φ)
  change ShortComplex.homologyMap ψ = 0
  apply (cancel_epi S.homologyπ).1
  apply (cancel_mono T.homologyι).1
  simp only [Category.assoc, comp_zero, zero_comp, ShortComplex.π_homologyMap_ι]
  have hb := cycles_comp_inr_eq_boundary φ i j hij
  have hd : (homotopyCofiber φ).d i j ≫ K.pOpcycles j = 0 :=
    K.d_pOpcycles i j
  have hz : (F.iCycles j ≫ φ.f j ≫ inrX φ j) ≫ K.pOpcycles j = 0 := by
    rw [hb]
    simpa only [Category.assoc, comp_zero] using
      congrArg (fun a : K.X i ⟶ K.opcycles j => (F.iCycles j ≫ inlX φ j i hij) ≫ a) hd
  change F.iCycles j ≫ (φ ≫ inr φ).f j ≫ K.pOpcycles j = 0
  rw [HomologicalComplex.comp_f, inr_f]
  simpa only [Category.assoc] using hz

end HomologicalComplex.homotopyCofiber
