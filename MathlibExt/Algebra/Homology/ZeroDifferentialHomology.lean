/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology of complexes with zero differential

When the incoming and outgoing differentials vanish, their kernel and
cokernel descriptions identify homology with the degree object. This
comparison is natural in the middle component of a chain map.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι}

/-- The actual native homology data of the original zero-differential short complex. -/
def zeroDifferentialHomologyData (K : HomologicalComplex C c) (i : ι)
    (h : ∀ j k, K.d j k = 0) : (K.sc i).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofZeros (K.sc i) (h _ _) (h _ _)

/-- Homology is the original degree object through the constructed native zero-map data. -/
def zeroDifferentialHomologyIso (K : HomologicalComplex C c) (i : ι)
    [K.HasHomology i] (h : ∀ j k, K.d j k = 0) : K.homology i ≅ K.X i :=
  (zeroDifferentialHomologyData K i h).homologyIso

/-- The native original homology class of any element of the original degree object. -/
def zeroDifferentialClassMap (K : HomologicalComplex C c) (i : ι)
    [K.HasHomology i] (h : ∀ j k, K.d j k = 0) : K.X i ⟶ K.homology i :=
  (K.sc i).liftCycles (𝟙 _) (by rw [Category.id_comp]; exact h _ _) ≫ (K.sc i).homologyπ

/-- The native class returns the same original element in the earned homology coordinates. -/
@[reassoc]
theorem zeroDifferentialClassMap_homologyIso (K : HomologicalComplex C c) (i : ι)
    [K.HasHomology i] (h : ∀ j k, K.d j k = 0) :
    zeroDifferentialClassMap K i h ≫ (zeroDifferentialHomologyIso K i h).hom = 𝟙 (K.X i) := by
  let S := K.sc i
  let H := zeroDifferentialHomologyData K i h
  let hk : (𝟙 S.X₂) ≫ S.g = 0 := by rw [Category.id_comp]; exact h _ _
  change (S.liftCycles (𝟙 _) hk ≫ S.homologyπ) ≫ H.homologyIso.hom = 𝟙 S.X₂
  rw [Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    ← Category.assoc, ShortComplex.LeftHomologyData.liftCycles_comp_cyclesIso_hom]
  have hl : H.liftK (𝟙 S.X₂) hk = 𝟙 S.X₂ := by
    have hi := H.liftK_i (𝟙 S.X₂) hk
    change H.liftK (𝟙 S.X₂) hk ≫ 𝟙 S.X₂ = 𝟙 S.X₂ at hi
    exact (Category.comp_id (H.liftK (𝟙 S.X₂) hk)).symm.trans hi
  change H.liftK (𝟙 S.X₂) hk ≫ 𝟙 S.X₂ = 𝟙 S.X₂
  erw [hl]
  exact Category.comp_id _

/-- The original middle-component map gives homology naturality. -/
@[reassoc]
theorem zeroDifferentialHomologyIso_naturality {K L : HomologicalComplex C c}
    (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hK : ∀ j k, K.d j k = 0) (hL : ∀ j k, L.d j k = 0) :
    homologyMap f i ≫ (zeroDifferentialHomologyIso L i hL).hom =
      (zeroDifferentialHomologyIso K i hK).hom ≫ f.f i := by
  let g := (shortComplexFunctor C c i).map f
  let H := ShortComplex.LeftHomologyMapData.ofZeros g (hK _ _) (hK _ _)
    (hL _ _) (hL _ _)
  exact H.homologyMap_comm

end HomologicalComplex
