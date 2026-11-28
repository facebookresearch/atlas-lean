/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/, Avocado

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageComparisonNaturality

import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Naturality of successor pages and iterated homology

Let C be an abelian category and f : K → L a map of bicomplexes of shape (down ℕ,down ℕ). The
homology map of the page-r map commutes with the successor isomorphisms H(E^r) ≅ E^{r+1}, for
every r≥1.

At page two, the comparison E²_{p,q} ≅ H_p(H_q^vertical(K)) is natural for f. It uses the
first-page row comparison normalized by (−1)^{p(q+1)}, with the fixed row embedded by p ↦
(p,q). The resulting naturality equation includes the boundary columns and rows of the first
quadrant.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Abelian Limits ComposableArrows

universe u v t k
namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type t} [Preorder ι] {X Y : SpectralObject C ι}

private theorem actual_EMap_indexing (phi : X ⟶ Y)
    {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (g₁ : j₀ ⟶ j₁) (g₂ : j₁ ⟶ j₂) (g₃ : j₂ ⟶ j₃)
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Hom.EMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        Y.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ =
      X.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ ≫
        Hom.EMap phi g₁ g₂ g₃ n₀ n₁ n₂ hn₁ hn₂ := by
  dsimp only [Hom.EMap, SpectralObject.map]
  apply ShortComplex.homologyMap_square
  apply ShortComplex.Hom.ext
  · exact ((phi.hom n₀).naturality _).symm
  · exact ((phi.hom n₁).naturality _).symm
  · exact ((phi.hom n₂).naturality _).symm

variable {κ : Type k} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

private def actual_pageHomologyData
    (X : SpectralObject C ι) (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data]
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    (((X.spectralSequence data).page r hr).sc x).HomologyData :=
  X.spectralSequenceHomologyData data r r' hrr' hr
    ((c r).prev x) x ((c r).next x) rfl rfl
    (data.i₀ r' x (by omega)) (data.i₀ r x hr) (data.i₁ x) (data.i₂ x)
    (data.i₃ r x hr) (data.i₃ r' x (by omega))
    rfl rfl rfl rfl rfl rfl
    (data.deg x - 1) (data.deg x) (data.deg x + 1) rfl (by omega) rfl

unseal spectralSequence in
private theorem actual_iso_pageHomologyData
    (X : SpectralObject C ι) (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data]
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    (X.spectralSequence data).iso r r' x hrr' hr =
      (actual_pageHomologyData X data r r' hrr' hr x).left.homologyIso := by
  simp only [spectralSequence, SpectralSequence.homologyIso,
    SpectralSequence.homologyIso', actual_pageHomologyData, spectralSequenceHomologyData,
    SpectralSequence.pageXIso, eqToIso_refl, Iso.refl_symm]
  exact Iso.trans_refl _

end CategoryTheory.Abelian.SpectralObject

namespace CategoryTheory.Abelian.SpectralObject
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

unseal spectralSequence in
private theorem actual_HD_i (X : SpectralObject C ι)
    (data : SpectralSequenceDataCore ι c r₀) [X.HasSpectralSequence data]
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    (actual_pageHomologyData X data r r' hrr' hr x).left.i =
      X.mapFourδ₁Toδ₀'
        (data.i₀ r' x (by omega)) (data.i₀ r x hr)
        (data.i₁ x) (data.i₂ x) (data.i₃ r x hr)
        (data.i₀_le r r' x hrr' hr) (data.le₀₁ r x hr)
        (data.le₁₂ x) (data.le₂₃ r x hr)
        (data.deg x - 1) (data.deg x) (data.deg x + 1) (by omega) rfl := by
  dsimp only [actual_pageHomologyData]
  rw [@spectralSequenceHomologyData_left_i]
  simp only [spectralSequencePageXIso, SpectralSequence.pageXIso,
    eqToIso_refl, Iso.refl_inv]
  exact Category.comp_id _

unseal spectralSequence in
private theorem actual_HD_π (X : SpectralObject C ι)
    (data : SpectralSequenceDataCore ι c r₀) [X.HasSpectralSequence data]
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    (actual_pageHomologyData X data r r' hrr' hr x).left.π =
      X.mapFourδ₄Toδ₃'
        (data.i₀ r' x (by omega)) (data.i₁ x) (data.i₂ x)
        (data.i₃ r x hr) (data.i₃ r' x (by omega))
        (data.le₀₁ r' x (by omega)) (data.le₁₂ x) (data.le₂₃ r x hr)
        (data.i₃_le r r' x hrr' hr)
        (data.deg x - 1) (data.deg x) (data.deg x + 1) (by omega) rfl := rfl

unseal spectralSequence in
private def actual_successorMapData {X Y : SpectralObject C ι}
    (phi : X ⟶ Y) (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor C (c r) x).map (phi.pageMap data r hr))
      (actual_pageHomologyData X data r r' hrr' hr x).left
      (actual_pageHomologyData Y data r r' hrr' hr x).left := by
  let hX := actual_pageHomologyData X data r r' hrr' hr x
  let hY := actual_pageHomologyData Y data r r' hrr' hr x
  let f := (HomologicalComplex.shortComplexFunctor C (c r) x).map (phi.pageMap data r hr)
  let k := Hom.EMap phi
    (homOfLE (data.le₀₁ r' x (by omega))) (homOfLE (data.le₁₂ x))
    (homOfLE (data.le₂₃ r x hr))
    (data.deg x - 1) (data.deg x) (data.deg x + 1) (by omega) rfl
  let h := (phi.pageMap data r' (by omega)).f x
  have hi : k ≫ hY.left.i = hX.left.i ≫ f.τ₂ := by
    dsimp only [hX, hY]
    rw [actual_HD_i, actual_HD_i]
    exact actual_EMap_indexing phi
      (homOfLE (data.le₀₁ r' x (by omega))) (homOfLE (data.le₁₂ x))
      (homOfLE (data.le₂₃ r x hr))
      (homOfLE (data.le₀₁ r x hr)) (homOfLE (data.le₁₂ x))
      (homOfLE (data.le₂₃ r x hr))
      (fourδ₁Toδ₀' (data.i₀ r' x (by omega)) (data.i₀ r x hr)
        (data.i₁ x) (data.i₂ x) (data.i₃ r x hr)
        (data.i₀_le r r' x hrr' hr) (data.le₀₁ r x hr)
        (data.le₁₂ x) (data.le₂₃ r x hr))
      (data.deg x - 1) (data.deg x) (data.deg x + 1) (by omega) rfl
  have hπ : hX.left.π ≫ h = k ≫ hY.left.π := by
    dsimp only [hX, hY]
    rw [actual_HD_π, actual_HD_π]
    exact (actual_EMap_indexing phi
      (homOfLE (data.le₀₁ r' x (by omega))) (homOfLE (data.le₁₂ x))
      (homOfLE (data.le₂₃ r x hr))
      (homOfLE (data.le₀₁ r' x (by omega))) (homOfLE (data.le₁₂ x))
      (homOfLE (data.le₂₃ r' x (by omega)))
      (fourδ₄Toδ₃' (data.i₀ r' x (by omega)) (data.i₁ x) (data.i₂ x)
        (data.i₃ r x hr) (data.i₃ r' x (by omega))
        (data.le₀₁ r' x (by omega)) (data.le₁₂ x) (data.le₂₃ r x hr)
        (data.i₃_le r r' x hrr' hr))
      (data.deg x - 1) (data.deg x) (data.deg x + 1) (by omega) rfl).symm
  refine { φK := k, φH := h, commi := hi, commπ := hπ, commf' := ?_ }
  apply (cancel_mono hY.left.i).1
  rw [Category.assoc, hi, ← Category.assoc,
    ShortComplex.LeftHomologyData.f'_i, Category.assoc,
    ShortComplex.LeftHomologyData.f'_i]
  exact f.comm₁₂.symm

unseal spectralSequence in
private theorem actual_pageMap_successor {X Y : SpectralObject C ι}
    (phi : X ⟶ Y) (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    HomologicalComplex.homologyMap (phi.pageMap data r hr) x ≫
        ((Y.spectralSequence data).iso r r' x hrr' hr).hom =
      ((X.spectralSequence data).iso r r' x hrr' hr).hom ≫
        (phi.pageMap data r' (by omega)).f x := by
  have h := (actual_successorMapData phi data r r' hrr' hr x).homologyMap_comm
  change HomologicalComplex.homologyMap (phi.pageMap data r hr) x ≫
      (actual_pageHomologyData Y data r r' hrr' hr x).left.homologyIso.hom =
    (actual_pageHomologyData X data r r' hrr' hr x).left.homologyIso.hom ≫
      (phi.pageMap data r' (by omega)).f x at h
  simpa only [actual_iso_pageHomologyData] using h

end CategoryTheory.Abelian.SpectralObject

namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
Let a¹ : E¹(K) → E¹(L) be its first-page map, a²_{p,q} its second-page component, and s_K,s_L
the successor isomorphisms H(E¹)_{p,q} ≅ E²_{p,q}. Then H_{(p,q)}(a¹) ≫ s_L.hom = s_K.hom ≫
a²_{p,q}. The homology is taken in the full first-page complex of bidegree (−1,0). -/
@[reassoc]
theorem horizontalPageMapOfBicomplex_successor_one_two
    (f : K ⟶ L) (p q : ℕ) :
    HomologicalComplex.homologyMap (horizontalPageMapOfBicomplex f 1 (le_refl 1)) (p, q) ≫
        ((horizontalFirstQuadrantSpectralSequence L).iso 1 2 (p, q)).hom =
      ((horizontalFirstQuadrantSpectralSequence K).iso 1 2 (p, q)).hom ≫
        horizontalSecondPageMapOfBicomplex f p q := by
  exact CategoryTheory.Abelian.SpectralObject.actual_pageMap_successor
    (horizontalCompleteFiltrationSpectralObjectMap f)
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
    1 2 rfl (by omega) (p, q)

private theorem horizontalSecondPageMapOfBicomplex_successor_inv
    (f : K ⟶ L) (p q : ℕ) :
    horizontalSecondPageMapOfBicomplex f p q ≫
        ((horizontalFirstQuadrantSpectralSequence L).iso 1 2 (p, q)).inv =
      ((horizontalFirstQuadrantSpectralSequence K).iso 1 2 (p, q)).inv ≫
        HomologicalComplex.homologyMap
          (horizontalPageMapOfBicomplex f 1 (le_refl 1)) (p, q) := by
  let eK := (horizontalFirstQuadrantSpectralSequence K).iso 1 2 (p, q)
  let eL := (horizontalFirstQuadrantSpectralSequence L).iso 1 2 (p, q)
  have h := horizontalPageMapOfBicomplex_successor_one_two f p q
  change horizontalSecondPageMapOfBicomplex f p q ≫ eL.inv =
    eK.inv ≫ HomologicalComplex.homologyMap
      (horizontalPageMapOfBicomplex f 1 (le_refl 1)) (p, q)
  apply (cancel_epi eK.hom).1
  calc
    eK.hom ≫ (horizontalSecondPageMapOfBicomplex f p q ≫ eL.inv) =
        (eK.hom ≫ horizontalSecondPageMapOfBicomplex f p q) ≫ eL.inv :=
      (Category.assoc _ _ _).symm
    _ = (HomologicalComplex.homologyMap
        (horizontalPageMapOfBicomplex f 1 (le_refl 1)) (p, q) ≫ eL.hom) ≫ eL.inv :=
      congrArg (fun z => z ≫ eL.inv) h.symm
    _ = HomologicalComplex.homologyMap
        (horizontalPageMapOfBicomplex f 1 (le_refl 1)) (p, q) := by
      rw [Category.assoc, eL.hom_inv_id, Category.comp_id]
    _ = eK.hom ≫ (eK.inv ≫ HomologicalComplex.homologyMap
        (horizontalPageMapOfBicomplex f 1 (le_refl 1)) (p, q)) := by simp

/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and p,q ∈ ℕ.
Let e_K : E²_{p,q}(K) ≅ H_p(K.verticalHomologyComplex q) and e_L be the comparisons obtained
from the first-page normalization (−1)^{a(q+1)} in column a. If a²_{p,q} is the second-page
map and v_q(f) the horizontal chain map on vertical homology induced by f, then a²_{p,q} ≫
e_L.hom = e_K.hom ≫ H_p(v_q(f)). -/
@[reassoc]
theorem horizontalSecondPageVerticalHorizontalHomologyIso_hom_naturality
    (f : K ⟶ L) (p q : ℕ) :
    horizontalSecondPageMapOfBicomplex f p q ≫
        (horizontalSecondPageVerticalHorizontalHomologyIso L p q).hom =
      (horizontalSecondPageVerticalHorizontalHomologyIso K p q).hom ≫
        HomologicalComplex.homologyMap (verticalHomologyComplexMap f q) p := by
  dsimp only [horizontalSecondPageVerticalHorizontalHomologyIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, horizontalSecondPageMapOfBicomplex_successor_inv]
  simp only [Category.assoc]
  rw [horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex_assoc]
  rw [horizontalFirstPageRowComplexIsoVerticalHomologyComplex_homology_naturality]

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- Let C be an abelian category, f : K → L a bicomplex map of shape (down ℕ,down ℕ), and r,r′ ∈ ℤ
with 1 ≤ r and r+1=r′. For p,q ∈ ℕ, let a^r be the fixed-page map and s_K,s_L : H(E^r)_{p,q} ≅
E^{r′}_{p,q} the successor isomorphisms. Then H_{(p,q)}(a^r) ≫ s_L.hom = s_K.hom ≫
a^{r′}_{p,q}. The degree-r page complex has differential bidegree (−r,r−1). -/
@[reassoc]
theorem horizontalPageMapOfBicomplex_successor
    (f : K ⟶ L) (r r' : ℤ) (hrr' : r + 1 = r') (hr : 1 ≤ r) (p q : ℕ) :
    HomologicalComplex.homologyMap (horizontalPageMapOfBicomplex f r hr) (p, q) ≫
        ((horizontalFirstQuadrantSpectralSequence L).iso r r' (p, q) hrr' hr).hom =
      ((horizontalFirstQuadrantSpectralSequence K).iso r r' (p, q) hrr' hr).hom ≫
        (horizontalPageMapOfBicomplex f r' (by omega)).f (p, q) := by
  exact CategoryTheory.Abelian.SpectralObject.actual_pageMap_successor
    (horizontalCompleteFiltrationSpectralObjectMap f)
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
    r r' hrr' hr (p, q)

end HomologicalComplex₂
