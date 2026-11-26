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

public import MathlibExt.Algebra.Homology.SpectralObjectPageMapNaturality
public import MathlibExt.Algebra.Homology.SpectralObjectMapNaturality
import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# Spectral-object maps and successor-page homology

Let C be an abelian category, ι a preorder, and data a spectral-sequence page
prescription with shape c_r on an independently sized set κ and initial page
r₀. At position pq the page object is
E^{d}(i₀(r,pq)≤i₁(pq)≤i₂(pq)≤i₃(r,pq)), with d=data.deg(pq).

For each spectral object, require the prescribed boundary vanishings:
H^{d+1}(i₀(r+1,pq)≤i₀(r,pq))=0 when pq has no outgoing c_r differential,
and H^{d−1}(i₃(r,pq)≤i₃(r+1,pq))=0 when pq has no incoming c_r
differential. These conditions give the successor-page identification
H_pq(E_r) ≅ E_{r+1,pq} for r≥r₀.

A morphism of spectral objects induces maps on these pages that commute with
the successor-page identifications. They form a spectral-sequence morphism,
respecting identities and composition. If the boundary conditions hold for
every spectral object, this construction is a functor from spectral objects
to spectral sequences.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

universe v u uι uκ

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Preorder ι]
variable {κ : Type uκ} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
variable {X Y Z : SpectralObject C ι}

namespace Hom

private abbrev successorHomologyData (X : SpectralObject C ι)
    (data : SpectralSequenceDataCore ι c r₀) [X.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    ((SpectralSequence.page X data r hr).sc pq).LeftHomologyData :=
  (SpectralSequence.homologyData X data r (r + 1) rfl hr
    ((c r).prev pq) pq ((c r).next pq) rfl rfl
    (data.i₀ (r + 1) pq) (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq)
    (data.i₃ r pq) (data.i₃ (r + 1) pq)
    rfl rfl rfl rfl rfl rfl
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl).left

private def successorCyclesMap (φ : X ⟶ Y)
    (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (successorHomologyData X data r hr pq).K ⟶
      (successorHomologyData Y data r hr pq).K :=
  φ.EMap (homOfLE (data.le₀₁ (r + 1) pq)) (homOfLE (data.le₁₂ pq))
    (homOfLE (data.le₂₃ r pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)

private theorem successorCyclesMap_commi (φ : X ⟶ Y)
    (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    successorCyclesMap φ data r hr pq ≫ (successorHomologyData Y data r hr pq).i =
      (successorHomologyData X data r hr pq).i ≫ (φ.pageMap data r hr).f pq := by
  let eX := SpectralSequence.pageXIso X data r hr pq
    (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq)
    rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl
  let eY := SpectralSequence.pageXIso Y data r hr pq
    (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq)
    rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl
  let mX := X.mapFourδ₁Toδ₀' (data.i₀ (r + 1) pq) (data.i₀ r pq)
    (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq)
    (data.i₀_le' rfl hr pq rfl rfl) (data.le₀₁ r pq)
    (data.le₁₂ pq) (data.le₂₃ r pq)
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
  let mY := Y.mapFourδ₁Toδ₀' (data.i₀ (r + 1) pq) (data.i₀ r pq)
    (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq)
    (data.i₀_le' rfl hr pq rfl rfl) (data.le₀₁ r pq)
    (data.le₁₂ pq) (data.le₂₃ r pq)
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
  have hMap : successorCyclesMap φ data r hr pq ≫ mY =
      mX ≫ φ.pageMapComponent data r hr pq :=
    (map_EMap φ _ _ _ _ _ _
      (fourδ₁Toδ₀' (data.i₀ (r + 1) pq) (data.i₀ r pq)
        (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq)
        (data.i₀_le' rfl hr pq rfl rfl) (data.le₀₁ r pq)
        (data.le₁₂ pq) (data.le₂₃ r pq))
      (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)).symm
  have hPage : φ.pageMapComponent data r hr pq ≫ eY.inv =
      eX.inv ≫ φ.pageMapComponent data r hr pq :=
    EMap_pageXIso_inv φ data r hr pq
      (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq)
      rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl
  change successorCyclesMap φ data r hr pq ≫ (mY ≫ eY.inv) =
    (mX ≫ eX.inv) ≫ φ.pageMapComponent data r hr pq
  rw [← Category.assoc, hMap, Category.assoc, hPage, ← Category.assoc]

private theorem successorHomologyMap_commπ (φ : X ⟶ Y)
    (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (successorHomologyData X data r hr pq).π ≫
        φ.pageMapComponent data (r + 1) (by omega) pq =
      successorCyclesMap φ data r hr pq ≫ (successorHomologyData Y data r hr pq).π := by
  change X.mapFourδ₄Toδ₃' (data.i₀ (r + 1) pq)
      (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq) (data.i₃ (r + 1) pq)
      (data.le₀₁ (r + 1) pq) (data.le₁₂ pq) (data.le₂₃ r pq)
      (data.le₃₃' rfl hr pq rfl rfl)
      (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) ≫ φ.EMap _ _ _ _ _ _ =
    φ.EMap _ _ _ _ _ _ ≫
      Y.mapFourδ₄Toδ₃' (data.i₀ (r + 1) pq)
        (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq) (data.i₃ (r + 1) pq)
        (data.le₀₁ (r + 1) pq) (data.le₁₂ pq) (data.le₂₃ r pq)
        (data.le₃₃' rfl hr pq rfl rfl)
        (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
  exact map_EMap φ _ _ _ _ _ _
    (fourδ₄Toδ₃' (data.i₀ (r + 1) pq)
      (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq) (data.i₃ (r + 1) pq)
      (data.le₀₁ (r + 1) pq) (data.le₁₂ pq) (data.le₂₃ r pq)
      (data.le₃₃' rfl hr pq rfl rfl))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)

private def successorLeftHomologyMapData (φ : X ⟶ Y)
    (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor C (c r) pq).map (φ.pageMap data r hr))
      (successorHomologyData X data r hr pq)
      (successorHomologyData Y data r hr pq) where
  φK := successorCyclesMap φ data r hr pq
  φH := φ.pageMapComponent data (r + 1) (by omega) pq
  commi := successorCyclesMap_commi φ data r hr pq
  commf' := by
    rw [← cancel_mono (successorHomologyData Y data r hr pq).i,
      Category.assoc, successorCyclesMap_commi, ← Category.assoc,
      ShortComplex.LeftHomologyData.f'_i, Category.assoc,
      ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor C (c r) pq).map
      (φ.pageMap data r hr)).comm₁₂.symm
  commπ := successorHomologyMap_commπ φ data r hr pq

private theorem pageMap_homologyIso (φ : X ⟶ Y)
    (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    HomologicalComplex.homologyMap (φ.pageMap data r hr) pq ≫
        (SpectralSequence.homologyIso Y data r (r + 1) rfl hr pq).hom =
      (SpectralSequence.homologyIso X data r (r + 1) rfl hr pq).hom ≫
        (φ.pageMap data (r + 1) (by omega)).f pq := by
  let eX := SpectralSequence.pageXIso X data (r + 1) (by omega) pq
    (data.i₀ (r + 1) pq) (data.i₁ pq) (data.i₂ pq) (data.i₃ (r + 1) pq)
    rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl
  let eY := SpectralSequence.pageXIso Y data (r + 1) (by omega) pq
    (data.i₀ (r + 1) pq) (data.i₁ pq) (data.i₂ pq) (data.i₃ (r + 1) pq)
    rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl
  have hHomology := (successorLeftHomologyMapData φ data r hr pq).homologyMap_comm
  change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor C (c r) pq).map (φ.pageMap data r hr)) ≫
      (successorHomologyData Y data r hr pq).homologyIso.hom =
    (successorHomologyData X data r hr pq).homologyIso.hom ≫
      φ.pageMapComponent data (r + 1) (by omega) pq at hHomology
  have hPage : φ.pageMapComponent data (r + 1) (by omega) pq ≫ eY.inv =
      eX.inv ≫ φ.pageMapComponent data (r + 1) (by omega) pq :=
    EMap_pageXIso_inv φ data (r + 1) (by omega) pq
      (data.i₀ (r + 1) pq) (data.i₁ pq) (data.i₂ pq) (data.i₃ (r + 1) pq)
      rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl
  change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor C (c r) pq).map (φ.pageMap data r hr)) ≫
      ((successorHomologyData Y data r hr pq).homologyIso.hom ≫ eY.inv) =
    ((successorHomologyData X data r hr pq).homologyIso.hom ≫ eX.inv) ≫
      φ.pageMapComponent data (r + 1) (by omega) pq
  rw [← Category.assoc, hHomology, Category.assoc, hPage, ← Category.assoc]

unseal SpectralObject.spectralSequence in
/-- Let C be abelian, ι a preorder, and data a common page prescription
with shapes c_r on κ and first page r₀. Let X and Y be spectral objects
indexed by ι. For both objects assume the prescribed boundary vanishings:
H^{d+1}(i₀(r+1,pq)≤i₀(r,pq)) is zero when pq has no outgoing c_r
differential, and H^{d−1}(i₃(r,pq)≤i₃(r+1,pq)) is zero when pq has no
incoming c_r differential, for r≥r₀ and d=data.deg(pq).

For φ:X → Y, r≥r₀, r′=r+1 and pq∈κ, let φ_r be the induced page map and
α_X:H_pq(E_r(X)) ≅ E_{r′,pq}(X), α_Y the successor-page isomorphisms.
Their compatibility square is
α_Y ∘ H_pq(φ_r) = (φ_{r′})_pq ∘ α_X. -/
@[reassoc]
theorem spectralSequencePageMap_comm (φ : X ⟶ Y)
    (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) :
    HomologicalComplex.homologyMap (φ.spectralSequencePageMap data r hr) pq ≫
        ((Y.spectralSequence data).iso r r' pq hrr' hr).hom =
      ((X.spectralSequence data).iso r r' pq hrr' hr).hom ≫
        (φ.spectralSequencePageMap data r' (by omega)).f pq := by
  subst r'
  exact pageMap_homologyIso φ data r hr pq

/-- Let C be abelian, ι a preorder, and data a common page prescription
with shapes c_r on κ and first page r₀. Let X and Y be spectral objects
indexed by ι. For both objects assume the prescribed boundary vanishings:
H^{d+1}(i₀(r+1,pq)≤i₀(r,pq)) is zero when pq has no outgoing c_r
differential, and H^{d−1}(i₃(r,pq)≤i₃(r+1,pq)) is zero when pq has no
incoming c_r differential, for r≥r₀ and d=data.deg(pq).

For a spectral-object morphism φ:X → Y, the spectral-sequence morphism
whose map on each page r≥r₀ is the map induced by φ on the prescribed
E-objects. It commutes with the isomorphisms from page homology to the
successor page. -/
def spectralSequenceMap (φ : X ⟶ Y)
    (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data] :
    X.spectralSequence data ⟶ Y.spectralSequence data where
  hom r hr := φ.spectralSequencePageMap data r hr
  comm r r' pq hrr' hr := spectralSequencePageMap_comm φ data r r' pq hrr' hr

@[simp]
theorem spectralSequenceMap_hom (φ : X ⟶ Y)
    (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) :
    (φ.spectralSequenceMap data).hom r hr = φ.spectralSequencePageMap data r hr :=
  rfl

unseal SpectralObject.spectralSequence in
/-- Let C be abelian, ι a preorder, and data a page prescription with shapes
c_r on κ and first page r₀. Let X be a spectral object indexed by ι,
satisfying the boundary vanishings
H^{d+1}(i₀(r+1,pq)≤i₀(r,pq))=0 at positions without an outgoing c_r
differential and H^{d−1}(i₃(r,pq)≤i₃(r+1,pq))=0 at positions without an
incoming c_r differential, for r≥r₀ and d=data.deg(pq).

The spectral-sequence morphism induced by the identity of X is the identity
of the spectral sequence prescribed by data. -/
@[simp]
theorem spectralSequenceMap_id (X : SpectralObject C ι)
    (data : SpectralSequenceDataCore ι c r₀) [X.HasSpectralSequence data] :
    spectralSequenceMap (𝟙 X) data = 𝟙 (X.spectralSequence data) := by
  apply CategoryTheory.SpectralSequence.hom_ext
  intro r hr
  exact pageMap_id X data r hr

unseal SpectralObject.spectralSequence in
/-- Let C be abelian, ι a preorder, and data a common page prescription with
shapes c_r on κ and first page r₀. Suppose spectral objects X, Y and Z
satisfy its boundary vanishings: the degree-(d+1) cohomology on
i₀(r+1,pq)≤i₀(r,pq) vanishes at positions without an outgoing c_r
differential, and the degree-(d−1) cohomology on
i₃(r,pq)≤i₃(r+1,pq) vanishes at positions without an incoming one.
For φ:X → Y and ψ:Y → Z, the spectral-sequence map induced by ψ∘φ
equals the composite of the maps induced by φ and ψ. -/
@[reassoc, simp]
theorem spectralSequenceMap_comp (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data] [Z.HasSpectralSequence data] :
    (φ ≫ ψ).spectralSequenceMap data =
      φ.spectralSequenceMap data ≫ ψ.spectralSequenceMap data := by
  apply CategoryTheory.SpectralSequence.hom_ext
  intro r hr
  exact pageMap_comp φ ψ data r hr

end Hom

/-- Let C be abelian, ι a preorder, and data a page prescription with shapes
c_r on κ beginning at r₀. Assume every spectral object W indexed by ι
satisfies its boundary vanishings: H_W^{d+1}(i₀(r+1,pq)≤i₀(r,pq))=0
where no outgoing c_r differential exists, and
H_W^{d−1}(i₃(r,pq)≤i₃(r+1,pq))=0 where no incoming c_r differential
exists, for r≥r₀ and d=data.deg(pq). The functor from spectral objects
to these spectral sequences sends W to its prescribed pages and a
morphism to the corresponding page maps. -/
def spectralObjectSpectralSequenceFunctor
    (data : SpectralSequenceDataCore ι c r₀)
    [∀ X : SpectralObject C ι, X.HasSpectralSequence data] :
    SpectralObject C ι ⥤ CategoryTheory.SpectralSequence C c r₀ where
  obj X := X.spectralSequence data
  map φ := φ.spectralSequenceMap data
  map_id X := Hom.spectralSequenceMap_id X data
  map_comp φ ψ := Hom.spectralSequenceMap_comp φ ψ data

@[simp]
theorem spectralObjectSpectralSequenceFunctor_obj
    (data : SpectralSequenceDataCore ι c r₀)
    [∀ X : SpectralObject C ι, X.HasSpectralSequence data] (X : SpectralObject C ι) :
    (spectralObjectSpectralSequenceFunctor data).obj X = X.spectralSequence data :=
  rfl

@[simp]
theorem spectralObjectSpectralSequenceFunctor_map
    (data : SpectralSequenceDataCore ι c r₀)
    [∀ X : SpectralObject C ι, X.HasSpectralSequence data] (φ : X ⟶ Y) :
    (spectralObjectSpectralSequenceFunctor data).map φ = φ.spectralSequenceMap data :=
  rfl

end CategoryTheory.Abelian.SpectralObject

end
