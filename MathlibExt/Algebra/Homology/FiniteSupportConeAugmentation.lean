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

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Actual cone augmentations and finite support

The stock cone of `φ : F ⟶ G` has the original summands `F.X (j + 1)`
and `G.X j`. Their original support windows give the cone window
`[min (a - 1) c, max (b - 1) e]`. Projectivity of their images gives
projectivity of the image cone terms through the stock biproduct charts.

An actual map from the image of `G` and an actual null homotopy of its
composite with the image of `φ` give an augmentation from the image cone.
Its component formula retains the original cone projections, map, and
null homotopy. This is glue data for induction on finite support.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uP vP uA vA

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCone

variable {P : Type uP} [Category.{vP} P] [Preadditive P] [HasBinaryBiproducts P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {F G : CochainComplex P ℤ} (φ : F ⟶ G)

/-- The original summand support windows give the exact computed cone
support window, including the shift of the source summand by one. -/
theorem isZero_outside_of_finiteSupport (a b c e : ℤ)
    (hF : ∀ j : ℤ, j < a ∨ b < j → IsZero (F.X j))
    (hG : ∀ j : ℤ, j < c ∨ e < j → IsZero (G.X j))
    (j : ℤ) (hj : j < min (a - 1) c ∨ max (b - 1) e < j) :
    IsZero ((CochainComplex.mappingCone φ).X j) := by
  apply (isZero_X_iff φ j).2
  rcases hj with hj | hj
  · have h₁ := min_le_left (a - 1) c
    have h₂ := min_le_right (a - 1) c
    exact ⟨hF (j + 1) (Or.inl (by omega)), hG j (Or.inl (by omega))⟩
  · have h₁ := le_max_left (b - 1) e
    have h₂ := le_max_right (b - 1) e
    exact ⟨hF (j + 1) (Or.inr (by omega)), hG j (Or.inr (by omega))⟩

/-- The original cone charts and the additive functor's biproduct chart
give projectivity of the actual image cone term. -/
theorem projective_image_term (i : P ⥤ A) [i.Additive]
    (hF : ∀ j : ℤ, Projective (i.obj (F.X j)))
    (hG : ∀ j : ℤ, Projective (i.obj (G.X j))) (j : ℤ) :
    Projective (i.obj ((CochainComplex.mappingCone φ).X j)) := by
  let _ : PreservesBinaryBiproducts i := preservesBinaryBiproducts_of_preservesBiproducts i
  let t : i.obj ((CochainComplex.mappingCone φ).X j) ≅
      i.obj (F.X (j + 1)) ⊞ i.obj (G.X j) :=
    i.mapIso (HomologicalComplex.homotopyCofiber.XIsoBiprod φ j (j + 1) rfl) ≪≫
      i.mapBiprod (F.X (j + 1)) (G.X j)
  let _ : Projective (i.obj (F.X (j + 1))) := hF (j + 1)
  let _ : Projective (i.obj (G.X j)) := hG j
  exact Projective.of_iso t.symm inferInstance

/-- The actual augmentation from the mapped stock cone, constructed from
the original target map and its actual null homotopy. -/
def mappedAugmentation (i : P ⥤ A) [i.Additive] {T : CochainComplex A ℤ}
    (β : (i.mapHomologicalComplex (.up ℤ)).obj G ⟶ T)
    (h : Homotopy ((i.mapHomologicalComplex (.up ℤ)).map φ ≫ β) 0) :
    (i.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCone φ) ⟶ T :=
  (mapHomologicalComplexIso φ i).hom ≫
    HomologicalComplex.homotopyCofiber.desc
      ((i.mapHomologicalComplex (.up ℤ)).map φ) β h

/-- The augmentation component is expressed through the actual original
cone projections and the original null homotopy and target map. -/
theorem mappedAugmentation_f (i : P ⥤ A) [i.Additive] {T : CochainComplex A ℤ}
    (β : (i.mapHomologicalComplex (.up ℤ)).obj G ⟶ T)
    (h : Homotopy ((i.mapHomologicalComplex (.up ℤ)).map φ ≫ β) 0) (j : ℤ) :
    (mappedAugmentation φ i β h).f j =
      i.map ((fst φ).1.v j (j + 1) rfl) ≫ h.hom (j + 1) j +
        i.map ((snd φ).v j j (add_zero j)) ≫ β.f j := by
  let ψ := (i.mapHomologicalComplex (.up ℤ)).map φ
  let E : (i.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCone φ) ≅
      CochainComplex.mappingCone ψ := mapHomologicalComplexIso φ i
  let D : CochainComplex.mappingCone ψ ⟶ T :=
    HomologicalComplex.homotopyCofiber.desc ψ β h
  have hE : E.hom.f j =
      i.map ((fst φ).1.v j (j + 1) rfl) ≫ (inl ψ).v (j + 1) j (by omega) +
        i.map ((snd φ).v j j (add_zero j)) ≫ (inr ψ).f j := by
    change (mapHomologicalComplexXIso' φ i j (j + 1) rfl).hom = _
    exact mapHomologicalComplexXIso'_hom φ i j (j + 1) rfl
  have hD₁ : (inl ψ).v (j + 1) j (by omega) ≫ D.f j = h.hom (j + 1) j :=
    HomologicalComplex.homotopyCofiber.inlX_desc_f ψ β h (j + 1) j rfl
  have hD₂ : (inr ψ).f j ≫ D.f j = β.f j :=
    HomologicalComplex.homotopyCofiber.inrX_desc_f ψ β h j
  change (E.hom ≫ D).f j = _
  calc
    _ = E.hom.f j ≫ D.f j := HomologicalComplex.comp_f E.hom D j
    _ = _ := by
      rw [hE]
      simp only [Preadditive.add_comp, Category.assoc, hD₁, hD₂]

/-- The mapped original right inclusion followed by the actual
augmentation is the original target map. -/
theorem mapped_inr_comp_mappedAugmentation (i : P ⥤ A) [i.Additive]
    {T : CochainComplex A ℤ} (β : (i.mapHomologicalComplex (.up ℤ)).obj G ⟶ T)
    (h : Homotopy ((i.mapHomologicalComplex (.up ℤ)).map φ ≫ β) 0) :
    (i.mapHomologicalComplex (.up ℤ)).map (inr φ) ≫ mappedAugmentation φ i β h = β := by
  let ψ := (i.mapHomologicalComplex (.up ℤ)).map φ
  let E : (i.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCone φ) ≅
      CochainComplex.mappingCone ψ := mapHomologicalComplexIso φ i
  let D : CochainComplex.mappingCone ψ ⟶ T :=
    HomologicalComplex.homotopyCofiber.desc ψ β h
  change (i.mapHomologicalComplex (.up ℤ)).map (inr φ) ≫ (E.hom ≫ D) = β
  calc
    _ = ((i.mapHomologicalComplex (.up ℤ)).map (inr φ) ≫ E.hom) ≫ D :=
      (Category.assoc _ _ _).symm
    _ = inr ψ ≫ D := congrArg (fun f => f ≫ D) (map_inr φ i)
    _ = β := HomologicalComplex.homotopyCofiber.inr_desc ψ β h

/-- Finite support and the original projective image terms earn
K-projectivity of the actual mapped stock cone. -/
theorem mappedCone_isKProjective (i : P ⥤ A) [i.Additive] (a b c e : ℤ)
    (hF : ∀ j : ℤ, j < a ∨ b < j → IsZero (F.X j))
    (hG : ∀ j : ℤ, j < c ∨ e < j → IsZero (G.X j))
    (hPF : ∀ j : ℤ, Projective (i.obj (F.X j)))
    (hPG : ∀ j : ℤ, Projective (i.obj (G.X j))) :
    CochainComplex.IsKProjective
      ((i.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCone φ)) := by
  let K : CochainComplex A ℤ :=
    (i.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCone φ)
  let _ : CochainComplex.IsStrictlyLE K (max (b - 1) e) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact i.map_isZero (isZero_outside_of_finiteSupport φ a b c e hF hG j (Or.inr hj))
  let _ : ∀ j : ℤ, Projective (K.X j) := projective_image_term φ i hPF hPG
  exact CochainComplex.isKProjective_of_projective K (max (b - 1) e)

end CochainComplex.mappingCone

end
