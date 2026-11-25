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

public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import Mathlib.Algebra.Ring.NegOnePow
public import MathlibExt.Algebra.Homology.SpectralObject.PageCore
public import MathlibExt.CategoryTheory.Monoidal.TensorCokernel
public import MathlibExt.Algebra.Homology.TensorHomologyDesc

/-!
# Pairings on the native pages of a spectral object

The primitive products in this file are products on the `H` intervals of
spectral objects. Their boundary rules concern the original triple boundary
maps. Products on cycles and their quotient pages are constructed from these
data. Tensoring is required to preserve cokernels; no tensor comparison with
homology is asserted to be an isomorphism.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type*} [Category* C] [Abelian C]

/-- The actual `H` object of a finite integer interval. -/
abbrev intervalH (X : SpectralObject C EInt) (n a b : ℤ) (hab : a ≤ b) : C :=
  (X.H n).obj (mk₁ (homOfLE (show (a : EInt) ≤ (b : EInt) by simpa using hab)))

/-- The actual covariant map between two finite intervals. -/
def intervalMap (X : SpectralObject C EInt) (n a b a' b' : ℤ)
    (hab : a ≤ b) (hab' : a' ≤ b') (ha : a ≤ a') (hb : b ≤ b') :
    X.intervalH n a b hab ⟶ X.intervalH n a' b' hab' :=
  (X.H n).map (homMk₁
    (homOfLE (show (a : EInt) ≤ (a' : EInt) by simpa using ha))
    (homOfLE (show (b : EInt) ≤ (b' : EInt) by simpa using hb)) (by cat_disch))

@[simp]
lemma intervalMap_id (X : SpectralObject C EInt) (n a b : ℤ) (hab : a ≤ b) :
    X.intervalMap n a b a b hab hab le_rfl le_rfl = 𝟙 _ := by
  change (X.H n).map _ = _
  convert CategoryTheory.Functor.map_id (X.H n) _ using 1
  congr 1

@[reassoc]
lemma intervalMap_comp (X : SpectralObject C EInt) (n a b a' b' a'' b'' : ℤ)
    (hab : a ≤ b) (hab' : a' ≤ b') (hab'' : a'' ≤ b'')
    (ha : a ≤ a') (hb : b ≤ b') (ha' : a' ≤ a'') (hb' : b' ≤ b'') :
    X.intervalMap n a b a' b' hab hab' ha hb ≫
        X.intervalMap n a' b' a'' b'' hab' hab'' ha' hb' =
      X.intervalMap n a b a'' b'' hab hab'' (ha.trans ha') (hb.trans hb') := by
  dsimp only [intervalMap]
  rw [← CategoryTheory.Functor.map_comp]
  congr 1

/-- The original triple boundary, with explicit integer degree transport. -/
abbrev intervalδ (X : SpectralObject C EInt) (n n' a b c : ℤ)
    (hab : a ≤ b) (hbc : b ≤ c) (hn : n + 1 = n') :
    X.intervalH n b c hbc ⟶ X.intervalH n' a b hab :=
  X.δ (homOfLE (show (a : EInt) ≤ (b : EInt) by simpa using hab))
    (homOfLE (show (b : EInt) ≤ (c : EInt) by simpa using hbc)) n n' hn

/-- The genuine cycles in a finite page window. -/
abbrev windowCycles (X : SpectralObject C EInt) (n a ℓ : ℤ) (hℓ : 1 ≤ ℓ) : C :=
  X.cycles (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by
    simp; omega)) (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp)) n

/-- The genuine quotient object of a finite page window. -/
abbrev windowE (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) : C :=
  X.E (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by
    simp; omega)) (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp))
    (homOfLE (show (a : EInt) ≤ ((a + u - 1 : ℤ) : EInt) by simp; omega))
    (n - 1) n (n + 1)

/-- The original long-interval representatives of the cycles. -/
abbrev windowToCycles (X : SpectralObject C EInt) (n a ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.intervalH n (a - ℓ) a (by omega) ⟶ X.windowCycles n a ℓ hℓ :=
  X.toCycles _ _ (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ (a : EInt) by simp; omega))
    (by cat_disch) n

/-- The original inclusion of the cycle kernel into the short interval. -/
abbrev windowICycles (X : SpectralObject C EInt) (n a ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.windowCycles n a ℓ hℓ ⟶ X.intervalH n (a - 1) a (by omega) :=
  X.iCycles _ _ n

/-- The original cycle quotient projection of a finite window. -/
abbrev windowπ (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    X.windowCycles n a ℓ hℓ ⟶ X.windowE n a ℓ u hℓ hu :=
  X.πE _ _ _ (n - 1) n (n + 1)

/-- The original last-interval boundary into the genuine cycles. -/
abbrev windowBoundary (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    X.intervalH (n - 1) a (a + u - 1) (by omega) ⟶ X.windowCycles n a ℓ hℓ :=
  X.δToCycles _ _ _ (n - 1) n

@[reassoc]
lemma windowToCycles_i (X : SpectralObject C EInt) (n a ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.windowToCycles n a ℓ hℓ ≫ X.windowICycles n a ℓ hℓ =
      X.intervalMap n (a - ℓ) a (a - 1) a (by omega) (by omega) (by omega) le_rfl := by
  rw [toCycles_i]
  congr 1

@[reassoc]
lemma windowBoundary_i (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    X.windowBoundary n a ℓ u hℓ hu ≫ X.windowICycles n a ℓ hℓ =
      X.intervalδ (n - 1) n (a - 1) a (a + u - 1) (by omega) (by omega) (by omega) := by
  apply δToCycles_iCycles

@[reassoc]
lemma windowBoundary_π (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    X.windowBoundary n a ℓ u hℓ hu ≫ X.windowπ n a ℓ u hℓ hu = 0 := by
  apply δToCycles_πE

/-- The native cycle quotient, as its actual colimit cofork. -/
def windowCofork (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    CokernelCofork (X.windowBoundary n a ℓ u hℓ hu) :=
  CokernelCofork.ofπ (X.windowπ n a ℓ u hℓ hu) (X.windowBoundary_π n a ℓ u hℓ hu)

/-- The original projection is a cokernel of the original last boundary. -/
def windowCoforkIsColimit (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) : IsColimit (X.windowCofork n a ℓ u hℓ hu) :=
  (X.cokernelSequenceCyclesE_exact _ _ _ (n - 1) n (n + 1)).gIsCokernel

/-- The native cycle map when the lower window is shortened. -/
def windowCyclesMap (X : SpectralObject C EInt) (n a ℓ ℓ' : ℤ)
    (hℓ : 1 ≤ ℓ) (hℓ' : 1 ≤ ℓ') (h : ℓ' ≤ ℓ) :
    X.windowCycles n a ℓ hℓ ⟶ X.windowCycles n a ℓ' hℓ' :=
  X.cyclesMap
    (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by simp; omega))
    (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp))
    (homOfLE (show ((a - ℓ' : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by simp; omega))
    (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp)) (homMk₂
    (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - ℓ' : ℤ) : EInt) by simp; omega))
    (𝟙 _) (𝟙 _) (by cat_disch) (by cat_disch)) n

@[reassoc (attr := simp)]
lemma windowCyclesMap_i (X : SpectralObject C EInt) (n a ℓ ℓ' : ℤ)
    (hℓ : 1 ≤ ℓ) (hℓ' : 1 ≤ ℓ') (h : ℓ' ≤ ℓ) :
    X.windowCyclesMap n a ℓ ℓ' hℓ hℓ' h ≫ X.windowICycles n a ℓ' hℓ' =
      X.windowICycles n a ℓ hℓ := by
  have hw := X.cyclesMap_i
    (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by simp; omega))
    (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp))
    (homOfLE (show ((a - ℓ' : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by simp; omega))
    (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp))
    (homMk₂ (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - ℓ' : ℤ) : EInt) by simp; omega))
      (𝟙 _) (𝟙 _) (by cat_disch) (by cat_disch)) (𝟙 _) n (by cat_disch)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hw
  with_unfolding_all exact hw

/-- The native interval-index map on a page quotient. -/
def windowMap (X : SpectralObject C EInt) (n a ℓ u ℓ' u' : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (hℓ' : 1 ≤ ℓ') (hu' : 1 ≤ u')
    (hℓ'ℓ : ℓ' ≤ ℓ) (huu' : u ≤ u') :
    X.windowE n a ℓ u hℓ hu ⟶ X.windowE n a ℓ' u' hℓ' hu' :=
  X.map
    (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by simp; omega))
    (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp))
    (homOfLE (show (a : EInt) ≤ ((a + u - 1 : ℤ) : EInt) by simp; omega))
    (homOfLE (show ((a - ℓ' : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by simp; omega))
    (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp))
    (homOfLE (show (a : EInt) ≤ ((a + u' - 1 : ℤ) : EInt) by simp; omega)) (homMk₃
    (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - ℓ' : ℤ) : EInt) by simp; omega))
    (𝟙 _) (𝟙 _)
    (homOfLE (show ((a + u - 1 : ℤ) : EInt) ≤ ((a + u' - 1 : ℤ) : EInt) by simp; omega))
    (by cat_disch) (by cat_disch) (by cat_disch)) (n - 1) n (n + 1)

@[reassoc (attr := simp)]
lemma windowπ_map (X : SpectralObject C EInt) (n a ℓ u ℓ' u' : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (hℓ' : 1 ≤ ℓ') (hu' : 1 ≤ u')
    (hℓ'ℓ : ℓ' ≤ ℓ) (huu' : u ≤ u') :
    X.windowπ n a ℓ u hℓ hu ≫ X.windowMap n a ℓ u ℓ' u' hℓ hu hℓ' hu' hℓ'ℓ huu' =
      X.windowCyclesMap n a ℓ ℓ' hℓ hℓ' hℓ'ℓ ≫ X.windowπ n a ℓ' u' hℓ' hu' := by
  dsimp only [windowMap, windowCyclesMap]
  exact X.πE_map _ _ _ _ _ _ _ _ (n - 1) n (n + 1) (by cat_disch) (by omega) rfl

/-- Canonical arithmetic transport of the output window; it only changes
an endpoint and the notation for consecutive degrees. -/
def windowOutputIso (X : SpectralObject C EInt) (n₀ n n₂ a ℓ u e : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (he : a ≤ e)
    (hn₀ : n₀ + 1 = n) (hn₂ : n + 1 = n₂) (he' : e = a + u - 1) :
    X.E (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by simp; omega))
      (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp))
      (homOfLE (show (a : EInt) ≤ (e : EInt) by simpa using he))
      n₀ n n₂ hn₀ hn₂ ≅ X.windowE n a ℓ u hℓ hu :=
  eqToIso (by
    obtain rfl : n₀ = n - 1 := by omega
    subst n₂ e
    rfl)

@[reassoc (attr := simp)]
lemma πE_windowOutputIso (X : SpectralObject C EInt) (n₀ n n₂ a ℓ u e : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (he : a ≤ e)
    (hn₀ : n₀ + 1 = n) (hn₂ : n + 1 = n₂) (he' : e = a + u - 1) :
    X.πE _ _ _ n₀ n n₂ hn₀ hn₂ ≫
        (X.windowOutputIso n₀ n n₂ a ℓ u e hℓ hu he hn₀ hn₂ he').hom =
      X.windowπ n a ℓ u hℓ hu := by
  obtain rfl : n₀ = n - 1 := by omega
  subst n₂ e
  simp only [windowOutputIso, eqToIso_refl, Iso.refl_hom, Category.comp_id]

/-- The native spectral-object differential of a symmetric integer window. -/
def windowD (X : SpectralObject C EInt) (n a r : ℤ) (hr : 1 ≤ r) :
    X.windowE n a r r hr hr ⟶ X.windowE (n + 1) (a - r) r r hr hr := by
  let f₁ : ((a - r - r : ℤ) : EInt) ⟶ ((a - r - 1 : ℤ) : EInt) :=
    homOfLE (by simp; omega)
  let f₂ : ((a - r - 1 : ℤ) : EInt) ⟶ ((a - r : ℤ) : EInt) := homOfLE (by simp)
  let f₃ : ((a - r : ℤ) : EInt) ⟶ ((a - 1 : ℤ) : EInt) := homOfLE (by simp; omega)
  let f₄ : ((a - 1 : ℤ) : EInt) ⟶ (a : EInt) := homOfLE (by simp)
  let f₅ : (a : EInt) ⟶ ((a + r - 1 : ℤ) : EInt) := homOfLE (by simp; omega)
  exact X.d f₁ f₂ f₃ f₄ f₅ (n - 1) n (n + 1) ((n + 1) + 1) ≫
    (X.windowOutputIso n (n + 1) ((n + 1) + 1) (a - r) r r (a - 1)
      hr hr (by omega) rfl rfl (by omega)).hom

@[reassoc (attr := simp)]
lemma representatives_windowD (X : SpectralObject C EInt) (n a r : ℤ) (hr : 1 ≤ r) :
    X.windowToCycles n a r hr ≫ X.windowπ n a r r hr hr ≫ X.windowD n a r hr =
      X.intervalδ n (n + 1) (a - r - r) (a - r) a (by omega) (by omega) rfl ≫
        X.windowToCycles (n + 1) (a - r) r hr ≫
          X.windowπ (n + 1) (a - r) r r hr hr := by
  dsimp only [windowD]
  rw [X.toCycles_πE_d_assoc _ _ _ _ _ _ (by cat_disch) _ (by cat_disch)
    (n - 1) n (n + 1) ((n + 1) + 1) (by omega) rfl rfl]
  rw [πE_windowOutputIso]
  congr 2 <;> cat_disch

/-- The canonical identification of a native page with its finite integer window. -/
def pageWindowIso (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).X pq ≅
      X.windowE (pq.1 + pq.2) (-pq.1) r r hr hr :=
  X.spectralSequencePageXIso skeletalPageCore r hr pq
    (-pq.1 - r : ℤ) (-pq.1 - 1 : ℤ) (-pq.1 : ℤ) (-pq.1 + r - 1 : ℤ)
    rfl rfl rfl rfl (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) rfl

/-- The same native page iso with independently chosen, equal degree and cut notation. -/
def pageWindowIsoAt (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ)
    (n a : ℤ) (hn : n = pq.1 + pq.2) (ha : a = -pq.1) :
    ((X.skeletalSpectralSequence).page r).X pq ≅ X.windowE n a r r hr hr := by
  subst n a
  exact X.pageWindowIso r hr pq

/-- The original page iso commutes with canonical endpoint and degree transport. -/
lemma pageWindowIsoAt_output (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) (n₀ n n₂ a e : ℤ) (hn : n = pq.1 + pq.2) (ha : a = -pq.1)
    (he : a ≤ e) (hn₀ : n₀ + 1 = n) (hn₂ : n + 1 = n₂) (he' : e = a + r - 1) :
    (X.spectralSequencePageXIso skeletalPageCore r hr pq
      (a - r : ℤ) (a - 1 : ℤ) (a : ℤ) (e : ℤ)
      (by subst a; rfl) (by subst a; rfl) (by subst a; rfl)
      (by subst e a; rfl) n₀ n n₂ hn hn₀ hn₂).hom ≫
        (X.windowOutputIso n₀ n n₂ a r r e hr hr he hn₀ hn₂ he').hom =
      (X.pageWindowIsoAt r hr pq n a hn ha).hom := by
  subst n a e
  obtain rfl : n₀ = pq.1 + pq.2 - 1 := by omega
  subst n₂
  simp only [windowOutputIso, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  rfl

/-- The displayed native page differential is exactly the original spectral-object
window differential, after canonical arithmetic transport. -/
lemma pageWindowIsoAt_d (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) (n a : ℤ) (hn : n = pq.1 + pq.2) (ha : a = -pq.1) :
    (X.pageWindowIsoAt r hr pq n a hn ha).inv ≫
      ((X.skeletalSpectralSequence).page r).d pq (pq + (r, 1 - r)) ≫
        (X.pageWindowIsoAt r hr (pq + (r, 1 - r)) (n + 1) (a - r)
          (by dsimp; omega) (by dsimp; omega)).hom = X.windowD n a r hr := by
  let f₁ : ((a - r - r : ℤ) : EInt) ⟶ ((a - r - 1 : ℤ) : EInt) := homOfLE (by simp; omega)
  let f₂ : ((a - r - 1 : ℤ) : EInt) ⟶ ((a - r : ℤ) : EInt) := homOfLE (by simp)
  let f₃ : ((a - r : ℤ) : EInt) ⟶ ((a - 1 : ℤ) : EInt) := homOfLE (by simp; omega)
  let f₄ : ((a - 1 : ℤ) : EInt) ⟶ (a : EInt) := homOfLE (by simp)
  let f₅ : (a : EInt) ⟶ ((a + r - 1 : ℤ) : EInt) := homOfLE (by simp; omega)
  have hd := X.spectralSequence_page_d_eq skeletalPageCore r hr pq (pq + (r, 1 - r)) rfl
    f₁ f₂ f₃ f₄ f₅
    (by congr 1; dsimp; omega) (by congr 1; dsimp; omega)
    (by subst a; rfl) (by subst a; rfl) (by subst a; rfl) (by subst a; rfl)
    (n - 1) n (n + 1) ((n + 1) + 1) hn (by omega) rfl rfl
  have hs := X.pageWindowIsoAt_output r hr pq (n - 1) n (n + 1) a (a + r - 1)
    hn ha (by omega) (by omega) rfl rfl
  simp only [windowOutputIso, eqToIso_refl, Iso.refl_hom, Category.comp_id] at hs
  have ht := X.pageWindowIsoAt_output r hr (pq + (r, 1 - r)) n (n + 1) ((n + 1) + 1)
    (a - r) (a - 1) (by dsimp; omega) (by dsimp; omega) (by omega) rfl rfl (by omega)
  rw [hd, hs]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← ht, Iso.inv_hom_id_assoc]
  rfl

@[reassoc]
lemma pageWindowIsoAt_inv_d (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) (n a : ℤ) (hn : n = pq.1 + pq.2) (ha : a = -pq.1) :
    (X.pageWindowIsoAt r hr pq n a hn ha).inv ≫
      ((X.skeletalSpectralSequence).page r).d pq (pq + (r, 1 - r)) =
      X.windowD n a r hr ≫
        (X.pageWindowIsoAt r hr (pq + (r, 1 - r)) (n + 1) (a - r)
          (by dsimp; omega) (by dsimp; omega)).inv := by
  rw [← cancel_mono (X.pageWindowIsoAt r hr (pq + (r, 1 - r)) (n + 1) (a - r)
    (by dsimp; omega) (by dsimp; omega)).hom]
  rw [Category.assoc, X.pageWindowIsoAt_d r hr pq n a hn ha]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The native homology data computing the next page, with its genuine
asymmetric cycle window and enlarged quotient window. -/
def pageWindowHomologyData (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) : (((X.skeletalSpectralSequence).page r).sc pq).HomologyData :=
  X.spectralSequenceHomologyData skeletalPageCore r (r + 1) rfl hr
    ((ComplexShape.up' (r, 1 - r)).prev pq) pq
    ((ComplexShape.up' (r, 1 - r)).next pq) rfl rfl
    (-pq.1 - (r + 1) : ℤ) (-pq.1 - r : ℤ) (-pq.1 - 1 : ℤ) (-pq.1 : ℤ)
    (-pq.1 + r - 1 : ℤ) (-pq.1 + (r + 1) - 1 : ℤ)
    rfl rfl rfl rfl rfl rfl
    (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) rfl

/-- Actual page cycles identify with the native asymmetric `E` window. -/
def pageCyclesWindowIso (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).cycles pq ≅
      X.windowE (pq.1 + pq.2) (-pq.1) (r + 1) r (by omega) hr :=
  (X.pageWindowHomologyData r hr pq).left.cyclesIso

/-- Actual page homology identifies with the next symmetric `E` window. -/
def pageHomologyWindowIso (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).homology pq ≅
      X.windowE (pq.1 + pq.2) (-pq.1) (r + 1) (r + 1) (by omega) (by omega) :=
  (X.pageWindowHomologyData r hr pq).left.homologyIso

@[reassoc]
lemma pageCyclesWindowIso_i (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) :
    (X.pageCyclesWindowIso r hr pq).hom ≫
      X.windowMap (pq.1 + pq.2) (-pq.1) (r + 1) r r r (by omega) hr hr hr
        (by omega) le_rfl ≫ (X.pageWindowIso r hr pq).inv =
      ((X.skeletalSpectralSequence).page r).iCycles pq := by
  have hi := (X.pageWindowHomologyData r hr pq).left.cyclesIso_hom_comp_i
  dsimp only [pageWindowHomologyData] at hi
  have hiD := X.spectralSequenceHomologyData_left_i skeletalPageCore r (r + 1) rfl hr
    ((ComplexShape.up' (r, 1 - r)).prev pq) pq
    ((ComplexShape.up' (r, 1 - r)).next pq) rfl rfl
    (-pq.1 - (r + 1) : ℤ) (-pq.1 - r : ℤ) (-pq.1 - 1 : ℤ) (-pq.1 : ℤ)
    (-pq.1 + r - 1 : ℤ) (-pq.1 + (r + 1) - 1 : ℤ)
    rfl rfl rfl rfl rfl rfl
    (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) rfl (by omega) rfl
  rw [hiD] at hi
  dsimp only [windowMap, pageWindowIso, pageCyclesWindowIso]
  convert hi using 1
  all_goals first | rfl | (congr 2 <;> cat_disch)

@[reassoc]
lemma pageHomologyWindowIso_π (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).homologyπ pq ≫
        (X.pageHomologyWindowIso r hr pq).hom =
      (X.pageCyclesWindowIso r hr pq).hom ≫
        X.windowMap (pq.1 + pq.2) (-pq.1) (r + 1) r (r + 1) (r + 1)
          (by omega) hr (by omega) (by omega) le_rfl (by omega) := by
  have hπ := (X.pageWindowHomologyData r hr pq).left.homologyπ_comp_homologyIso_hom
  dsimp only [pageWindowHomologyData] at hπ
  have hπD := X.spectralSequenceHomologyData_left_π skeletalPageCore r (r + 1) rfl hr
    ((ComplexShape.up' (r, 1 - r)).prev pq) pq
    ((ComplexShape.up' (r, 1 - r)).next pq) rfl rfl
    (-pq.1 - (r + 1) : ℤ) (-pq.1 - r : ℤ) (-pq.1 - 1 : ℤ) (-pq.1 : ℤ)
    (-pq.1 + r - 1 : ℤ) (-pq.1 + (r + 1) - 1 : ℤ)
    rfl rfl rfl rfl rfl rfl
    (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) rfl (by omega) rfl
  rw [hπD] at hπ
  dsimp only [windowMap, pageCyclesWindowIso, pageHomologyWindowIso]
  convert hπ using 1
  all_goals first | rfl | (congr 2 <;> cat_disch)

unseal spectralSequence in
/-- This is the native successor isomorphism, followed by the next-page window iso. -/
@[reassoc]
lemma pageHomologyWindowIso_successor (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).iso r (r + 1) pq rfl hr).hom ≫
        (X.pageWindowIso (r + 1) (by omega) pq).hom =
      (X.pageHomologyWindowIso r hr pq).hom := by
  have hSS := X.spectralSequence_iso skeletalPageCore r (r + 1) rfl hr
    ((ComplexShape.up' (r, 1 - r)).prev pq) pq
    ((ComplexShape.up' (r, 1 - r)).next pq) rfl rfl
    (-pq.1 - (r + 1) : ℤ) (-pq.1 - r : ℤ) (-pq.1 - 1 : ℤ) (-pq.1 : ℤ)
    (-pq.1 + r - 1 : ℤ) (-pq.1 + (r + 1) - 1 : ℤ)
    rfl rfl rfl rfl rfl rfl
    (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) rfl (by omega) rfl
  with_unfolding_all rw [hSS, HomologicalComplex.homologyIsoSc'_eq_refl]
  with_unfolding_all change
    (𝟙 _ ≫ (X.pageHomologyWindowIso r hr pq).hom ≫
      (X.pageWindowIso (r + 1) (by omega) pq).inv) ≫
        (X.pageWindowIso (r + 1) (by omega) pq).hom =
      (X.pageHomologyWindowIso r hr pq).hom
  simp only [Category.assoc, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

@[reassoc]
lemma pageCyclesWindowIso_inv_i (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) :
    (X.pageCyclesWindowIso r hr pq).inv ≫ ((X.skeletalSpectralSequence).page r).iCycles pq =
      X.windowMap (pq.1 + pq.2) (-pq.1) (r + 1) r r r (by omega) hr hr hr
        (by omega) le_rfl ≫ (X.pageWindowIso r hr pq).inv := by
  rw [← X.pageCyclesWindowIso_i r hr pq, Iso.inv_hom_id_assoc]

@[reassoc]
lemma pageCyclesWindowIso_i_page (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).iCycles pq ≫ (X.pageWindowIso r hr pq).hom =
      (X.pageCyclesWindowIso r hr pq).hom ≫
        X.windowMap (pq.1 + pq.2) (-pq.1) (r + 1) r r r (by omega) hr hr hr
          (by omega) le_rfl := by
  rw [← X.pageCyclesWindowIso_i r hr pq]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc]
lemma pageCyclesWindowIso_inv_π (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) :
    (X.pageCyclesWindowIso r hr pq).inv ≫ ((X.skeletalSpectralSequence).page r).homologyπ pq =
      X.windowMap (pq.1 + pq.2) (-pq.1) (r + 1) r (r + 1) (r + 1)
        (by omega) hr (by omega) (by omega) le_rfl (by omega) ≫
          (X.pageHomologyWindowIso r hr pq).inv := by
  rw [← cancel_mono (X.pageHomologyWindowIso r hr pq).hom]
  simp only [Category.assoc, pageHomologyWindowIso_π, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- A boundary-compatible pairing of the original finite `H` intervals.

The three target inequalities express the usual product interval
`(max (a+d) (b+c), b+d)` followed by an actual interval map. The only
derivation rule here is a rule for original triple boundaries. -/
structure IntervalPairing (X Y Z : SpectralObject C EInt) where
  /-- Pair interval cohomology classes into the indicated target interval in total degree `n + m`. -/
  pair (n m k a b c d s t : ℤ) (hnm : n + m = k)
    (hab : a ≤ b) (hcd : c ≤ d) (hst : s ≤ t)
    (hleft : a + d ≤ s) (hright : b + c ≤ s) (hupper : b + d ≤ t) :
      X.intervalH n a b hab ⊗ Y.intervalH m c d hcd ⟶ Z.intervalH k s t hst
  naturality (n m k a b c d s t a' b' c' d' s' t' : ℤ)
    (hnm : n + m = k)
    (hab : a ≤ b) (hcd : c ≤ d) (hst : s ≤ t)
    (hab' : a' ≤ b') (hcd' : c' ≤ d') (hst' : s' ≤ t')
    (hleft : a + d ≤ s) (hright : b + c ≤ s) (hupper : b + d ≤ t)
    (hleft' : a' + d' ≤ s') (hright' : b' + c' ≤ s') (hupper' : b' + d' ≤ t')
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d')
    (hs : s ≤ s') (ht : t ≤ t') :
      (X.intervalMap n a b a' b' hab hab' ha hb ⊗ₘ
        Y.intervalMap m c d c' d' hcd hcd' hc hd) ≫
          pair n m k a' b' c' d' s' t' hnm hab' hcd' hst' hleft' hright' hupper' =
        pair n m k a b c d s t hnm hab hcd hst hleft hright hupper ≫
          Z.intervalMap k s t s' t' hst hst' hs ht
  boundary_left (n m a b ℓ u : ℤ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
      (X.intervalδ (n - 1) n (a - 1) a (a + u - 1) (by omega) (by omega)
          (by omega) ⊗ₘ
        Y.intervalMap m (b - ℓ) b (b - 1) b (by omega) (by omega)
          (by omega) le_rfl) ≫
          pair n m (n + m) (a - 1) a (b - 1) b (a + b - 1) (a + b)
            rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) =
        pair (n - 1) m (n + m - 1) a (a + u - 1) (b - ℓ) b
          (a + b) (a + b + u - 1) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ≫
          Z.intervalδ (n + m - 1) (n + m) (a + b - 1) (a + b) (a + b + u - 1)
            (by omega) (by omega) (by omega)
  boundary_right (n m a b ℓ u : ℤ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
      (X.intervalMap n (a - ℓ) a (a - 1) a (by omega) (by omega)
          (by omega) le_rfl ⊗ₘ
        Y.intervalδ (m - 1) m (b - 1) b (b + u - 1) (by omega) (by omega)
          (by omega)) ≫
          pair n m (n + m) (a - 1) a (b - 1) b (a + b - 1) (a + b)
            rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) =
        (n.negOnePow : ℤ) •
          (pair n (m - 1) (n + m - 1) (a - ℓ) a b (b + u - 1)
            (a + b) (a + b + u - 1) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ≫
            Z.intervalδ (n + m - 1) (n + m) (a + b - 1) (a + b) (a + b + u - 1)
              (by omega) (by omega) (by omega))
  boundary_aligned (n m a b r : ℤ) (hr : 1 ≤ r) :
      pair n m (n + m) (a - r) a (b - r) b (a + b - r) (a + b)
          rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ≫
        Z.intervalδ (n + m) (n + m + 1) (a + b - r - r) (a + b - r) (a + b)
          (by omega) (by omega) rfl =
      (X.intervalδ n (n + 1) (a - r - r) (a - r) a
          (by omega) (by omega) rfl ⊗ₘ 𝟙 _) ≫
        pair (n + 1) m (n + m + 1) (a - r - r) (a - r) (b - r) b
          (a + b - r - r) (a + b - r) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) +
      (n.negOnePow : ℤ) •
        ((𝟙 _ ⊗ₘ Y.intervalδ m (m + 1) (b - r - r) (b - r) b
            (by omega) (by omega) rfl) ≫
          pair n (m + 1) (n + m + 1) (a - r) a (b - r - r) (b - r)
            (a + b - r - r) (a + b - r) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))

variable [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)]

private lemma epi_tensorHom_of_cokernels {A B D F : C} (f : A ⟶ B) (g : D ⟶ F)
    [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  let c₁ : CokernelCofork (kernel.ι f) := CokernelCofork.ofπ f (kernel.condition f)
  let c₂ : CokernelCofork (kernel.ι g) := CokernelCofork.ofπ g (kernel.condition g)
  exact CokernelCofork.epi_tensor_π c₁
    (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)) c₂
    (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _))

namespace IntervalPairing

variable {X Y Z : SpectralObject C EInt} (P : IntervalPairing X Y Z)

/-- The original product on the short intervals of a page. -/
def shortPair (n m k : ℤ) (hnm : n + m = k) (a b : ℤ) :
    X.intervalH n (a - 1) a (by omega) ⊗ Y.intervalH m (b - 1) b (by omega) ⟶
      Z.intervalH k (a + b - 1) (a + b) (by omega) :=
  P.pair n m k (a - 1) a (b - 1) b (a + b - 1) (a + b)
    hnm (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The original product on the long intervals representing page cycles. -/
def longPair (n m k : ℤ) (hnm : n + m = k) (a b ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.intervalH n (a - ℓ) a (by omega) ⊗ Y.intervalH m (b - ℓ) b (by omega) ⟶
      Z.intervalH k (a + b - ℓ) (a + b) (by omega) :=
  P.pair n m k (a - ℓ) a (b - ℓ) b (a + b - ℓ) (a + b)
    hnm (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

-- Keep the original hypothesis parameters and their order in this compatibility declaration.
@[reassoc, nolint unusedArguments]
lemma longPair_restriction (n m k : ℤ) (hnm : n + m = k) (a b ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    (X.intervalMap n (a - ℓ) a (a - 1) a (by omega) (by omega) (by omega) le_rfl ⊗ₘ
      Y.intervalMap m (b - ℓ) b (b - 1) b (by omega) (by omega) (by omega) le_rfl) ≫
        P.shortPair n m k hnm a b =
      P.longPair n m k hnm a b ℓ hℓ ≫
        Z.intervalMap k (a + b - ℓ) (a + b) (a + b - 1) (a + b)
          (by omega) (by omega) (by omega) le_rfl :=
  P.naturality n m k (a - ℓ) a (b - ℓ) b (a + b - ℓ) (a + b)
    (a - 1) a (b - 1) b (a + b - 1) (a + b) hnm
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) le_rfl (by omega) le_rfl (by omega) le_rfl

lemma cyclesPair_boundary_zero (n m k : ℤ) (hnm : n + m = k)
    (a b ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    (X.windowICycles n a ℓ hℓ ⊗ₘ Y.windowICycles m b ℓ hℓ) ≫
        P.shortPair n m k hnm a b ≫
          Z.intervalδ k (k + 1) (a + b - ℓ) (a + b - 1) (a + b)
            (by omega) (by omega) rfl = 0 := by
  letI : Epi (X.windowToCycles n a ℓ hℓ ⊗ₘ Y.windowToCycles m b ℓ hℓ) :=
    epi_tensorHom_of_cokernels _ _
  rw [← cancel_epi (X.windowToCycles n a ℓ hℓ ⊗ₘ Y.windowToCycles m b ℓ hℓ),
    comp_zero, ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom,
    windowToCycles_i, windowToCycles_i, P.longPair_restriction n m k hnm a b ℓ hℓ]
  rw [← Z.windowToCycles_i k (a + b) ℓ hℓ]
  simp only [Category.assoc, iCycles_δ, comp_zero]

/-- The product on genuine cycles is a kernel lift of the original short product. -/
def cyclesPair (n m k : ℤ) (hnm : n + m = k) (a b ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.windowCycles n a ℓ hℓ ⊗ Y.windowCycles m b ℓ hℓ ⟶
      Z.windowCycles k (a + b) ℓ hℓ :=
  Z.liftCycles _ _ k (k + 1) rfl
    ((X.windowICycles n a ℓ hℓ ⊗ₘ Y.windowICycles m b ℓ hℓ) ≫
      P.shortPair n m k hnm a b) (by simpa only [Category.assoc] using P.cyclesPair_boundary_zero n m k hnm a b ℓ hℓ)

@[reassoc (attr := simp)]
lemma cyclesPair_i (n m k : ℤ) (hnm : n + m = k) (a b ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    P.cyclesPair n m k hnm a b ℓ hℓ ≫ Z.windowICycles k (a + b) ℓ hℓ =
      (X.windowICycles n a ℓ hℓ ⊗ₘ Y.windowICycles m b ℓ hℓ) ≫
        P.shortPair n m k hnm a b := by
  apply liftCycles_i

@[reassoc (attr := simp)]
lemma toCycles_cyclesPair (n m k : ℤ) (hnm : n + m = k) (a b ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    (X.windowToCycles n a ℓ hℓ ⊗ₘ Y.windowToCycles m b ℓ hℓ) ≫
        P.cyclesPair n m k hnm a b ℓ hℓ =
      P.longPair n m k hnm a b ℓ hℓ ≫ Z.windowToCycles k (a + b) ℓ hℓ := by
  rw [← cancel_mono (Z.windowICycles k (a + b) ℓ hℓ)]
  simp only [Category.assoc, cyclesPair_i, windowToCycles_i]
  rw [← Category.assoc, tensorHom_comp_tensorHom, windowToCycles_i,
    windowToCycles_i, P.longPair_restriction n m k hnm a b ℓ hℓ]

/-- Multiplying an original left boundary by a long representative gives
an original boundary in the product window. -/
@[reassoc]
lemma boundary_left_cyclesPair (n m k : ℤ) (hnm : n + m = k)
    (a b ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    (X.windowBoundary n a ℓ u hℓ hu ⊗ₘ Y.windowToCycles m b ℓ hℓ) ≫
        P.cyclesPair n m k hnm a b ℓ hℓ =
      P.pair (n - 1) m (k - 1) a (a + u - 1) (b - ℓ) b
        (a + b) (a + b + u - 1) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ≫
          Z.windowBoundary k (a + b) ℓ u hℓ hu := by
  subst k
  rw [← cancel_mono (Z.windowICycles (n + m) (a + b) ℓ hℓ)]
  simp only [Category.assoc, cyclesPair_i, windowBoundary_i]
  rw [← Category.assoc, tensorHom_comp_tensorHom, windowBoundary_i, windowToCycles_i]
  exact P.boundary_left n m a b ℓ u hu huℓ

/-- Multiplying an original right boundary by a long representative gives
an original boundary, with the integer total-degree sign. -/
@[reassoc]
lemma boundary_right_cyclesPair (n m k : ℤ) (hnm : n + m = k)
    (a b ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    (X.windowToCycles n a ℓ hℓ ⊗ₘ Y.windowBoundary m b ℓ u hℓ hu) ≫
        P.cyclesPair n m k hnm a b ℓ hℓ =
      (n.negOnePow : ℤ) •
        (P.pair n (m - 1) (k - 1) (a - ℓ) a b (b + u - 1)
          (a + b) (a + b + u - 1) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ≫
            Z.windowBoundary k (a + b) ℓ u hℓ hu) := by
  subst k
  rw [← cancel_mono (Z.windowICycles (n + m) (a + b) ℓ hℓ)]
  simp only [Category.assoc, cyclesPair_i, Preadditive.zsmul_comp, windowBoundary_i]
  rw [← Category.assoc, tensorHom_comp_tensorHom, windowToCycles_i, windowBoundary_i]
  exact P.boundary_right n m a b ℓ u hu huℓ

lemma left_boundary_zero (n m k : ℤ) (hnm : n + m = k)
    (a b ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    (X.windowBoundary n a ℓ u hℓ hu ▷ Y.windowCycles m b ℓ hℓ) ≫
        P.cyclesPair n m k hnm a b ℓ hℓ ≫ Z.windowπ k (a + b) ℓ u hℓ hu = 0 := by
  letI : Epi (𝟙 (X.intervalH (n - 1) a (a + u - 1) (by omega)) ⊗ₘ
      Y.windowToCycles m b ℓ hℓ) := epi_tensorHom_of_cokernels _ _
  have hwh : (X.windowBoundary n a ℓ u hℓ hu ▷ Y.windowCycles m b ℓ hℓ) =
      (X.windowBoundary n a ℓ u hℓ hu ⊗ₘ 𝟙 _) := by simp [tensorHom_def]
  rw [hwh, ← cancel_epi (𝟙 _ ⊗ₘ Y.windowToCycles m b ℓ hℓ), comp_zero,
    ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Category.comp_id]
  rw [Category.assoc, P.boundary_left_cyclesPair_assoc n m k hnm a b ℓ u hℓ hu huℓ]
  simp only [Category.assoc, windowBoundary_π, comp_zero]

lemma right_boundary_zero (n m k : ℤ) (hnm : n + m = k)
    (a b ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    (X.windowCycles n a ℓ hℓ ◁ Y.windowBoundary m b ℓ u hℓ hu) ≫
        P.cyclesPair n m k hnm a b ℓ hℓ ≫ Z.windowπ k (a + b) ℓ u hℓ hu = 0 := by
  letI : Epi (X.windowToCycles n a ℓ hℓ ⊗ₘ
      𝟙 (Y.intervalH (m - 1) b (b + u - 1) (by omega))) := epi_tensorHom_of_cokernels _ _
  have hwh : (X.windowCycles n a ℓ hℓ ◁ Y.windowBoundary m b ℓ u hℓ hu) =
      (𝟙 _ ⊗ₘ Y.windowBoundary m b ℓ u hℓ hu) := by simp [tensorHom_def']
  rw [hwh, ← cancel_epi (X.windowToCycles n a ℓ hℓ ⊗ₘ 𝟙 _), comp_zero,
    ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Category.comp_id]
  rw [Category.assoc, P.boundary_right_cyclesPair_assoc n m k hnm a b ℓ u hℓ hu huℓ]
  simp only [Preadditive.zsmul_comp, Category.assoc, windowBoundary_π, comp_zero, smul_zero]

/-- The actual two boundary relations vanish after the product cycle quotient. -/
lemma boundaries_quotient_zero (n m k : ℤ) (hnm : n + m = k)
    (a b ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    coprod.desc
        (X.windowBoundary n a ℓ u hℓ hu ▷ Y.windowCycles m b ℓ hℓ)
        (X.windowCycles n a ℓ hℓ ◁ Y.windowBoundary m b ℓ u hℓ hu) ≫
      (P.cyclesPair n m k hnm a b ℓ hℓ ≫ Z.windowπ k (a + b) ℓ u hℓ hu) = 0 := by
  apply coprod.hom_ext
  · simpa only [coprod.inl_desc_assoc, comp_zero] using
      P.left_boundary_zero n m k hnm a b ℓ u hℓ hu huℓ
  · simpa only [coprod.inr_desc_assoc, comp_zero] using
      P.right_boundary_zero n m k hnm a b ℓ u hℓ hu huℓ

/-- The product on genuine `E` windows, obtained by descending the cycle product
through the native quotient projections. -/
def windowPair (n m k : ℤ) (hnm : n + m = k)
    (a b ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    X.windowE n a ℓ u hℓ hu ⊗ Y.windowE m b ℓ u hℓ hu ⟶
      Z.windowE k (a + b) ℓ u hℓ hu :=
  CokernelCofork.tensorDesc
    (X.windowCofork n a ℓ u hℓ hu) (X.windowCoforkIsColimit n a ℓ u hℓ hu)
    (Y.windowCofork m b ℓ u hℓ hu) (Y.windowCoforkIsColimit m b ℓ u hℓ hu)
    (P.cyclesPair n m k hnm a b ℓ hℓ ≫ Z.windowπ k (a + b) ℓ u hℓ hu)
    (P.boundaries_quotient_zero n m k hnm a b ℓ u hℓ hu huℓ)

@[reassoc (attr := simp)]
lemma quotient_windowPair (n m k : ℤ) (hnm : n + m = k)
    (a b ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    (X.windowπ n a ℓ u hℓ hu ⊗ₘ Y.windowπ m b ℓ u hℓ hu) ≫
        P.windowPair n m k hnm a b ℓ u hℓ hu huℓ =
      P.cyclesPair n m k hnm a b ℓ hℓ ≫ Z.windowπ k (a + b) ℓ u hℓ hu :=
  CokernelCofork.tensor_π_desc
    (X.windowCofork n a ℓ u hℓ hu) (X.windowCoforkIsColimit n a ℓ u hℓ hu)
    (Y.windowCofork m b ℓ u hℓ hu) (Y.windowCoforkIsColimit m b ℓ u hℓ hu)
    (P.cyclesPair n m k hnm a b ℓ hℓ ≫ Z.windowπ k (a + b) ℓ u hℓ hu)
    (P.boundaries_quotient_zero n m k hnm a b ℓ u hℓ hu huℓ)

@[reassoc (attr := simp)]
lemma representatives_windowPair (n m k : ℤ) (hnm : n + m = k)
    (a b ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    ((X.windowToCycles n a ℓ hℓ ≫ X.windowπ n a ℓ u hℓ hu) ⊗ₘ
      (Y.windowToCycles m b ℓ hℓ ≫ Y.windowπ m b ℓ u hℓ hu)) ≫
        P.windowPair n m k hnm a b ℓ u hℓ hu huℓ =
      P.longPair n m k hnm a b ℓ hℓ ≫
        Z.windowToCycles k (a + b) ℓ hℓ ≫ Z.windowπ k (a + b) ℓ u hℓ hu := by
  rw [← tensorHom_comp_tensorHom_assoc, quotient_windowPair,
    ← Category.assoc, toCycles_cyclesPair, Category.assoc]

/-- Arithmetic transport of the product to an explicitly chosen sum cut. -/
def windowPairTo (n m k : ℤ) (hnm : n + m = k) (a b s : ℤ) (hs : a + b = s)
    (ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    X.windowE n a ℓ u hℓ hu ⊗ Y.windowE m b ℓ u hℓ hu ⟶
      Z.windowE k s ℓ u hℓ hu := by
  subst s
  exact P.windowPair n m k hnm a b ℓ u hℓ hu huℓ

@[reassoc]
lemma representatives_windowPairTo (n m k : ℤ) (hnm : n + m = k)
    (a b s : ℤ) (hs : a + b = s) (ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    ((X.windowToCycles n a ℓ hℓ ≫ X.windowπ n a ℓ u hℓ hu) ⊗ₘ
      (Y.windowToCycles m b ℓ hℓ ≫ Y.windowπ m b ℓ u hℓ hu)) ≫
        P.windowPairTo n m k hnm a b s hs ℓ u hℓ hu huℓ =
      P.pair n m k (a - ℓ) a (b - ℓ) b (s - ℓ) s hnm
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ≫
        Z.windowToCycles k s ℓ hℓ ≫ Z.windowπ k s ℓ u hℓ hu := by
  subst s
  exact P.representatives_windowPair n m k hnm a b ℓ u hℓ hu huℓ

@[reassoc]
lemma representatives_left_differential_product (n m k : ℤ) (hnm : n + m = k)
    (a b r : ℤ) (hr : 1 ≤ r) :
    ((X.windowToCycles n a r hr ≫ X.windowπ n a r r hr hr) ⊗ₘ
      (Y.windowToCycles m b r hr ≫ Y.windowπ m b r r hr hr)) ≫
      (X.windowD n a r hr ⊗ₘ 𝟙 _) ≫
        P.windowPairTo (n + 1) m (k + 1) (by omega) (a - r) b (a + b - r)
          (by omega) r r hr hr le_rfl =
      (X.intervalδ n (n + 1) (a - r - r) (a - r) a (by omega) (by omega) rfl ⊗ₘ
        𝟙 (Y.intervalH m (b - r) b (by omega))) ≫
          P.pair (n + 1) m (k + 1) (a - r - r) (a - r) (b - r) b
            (a + b - r - r) (a + b - r) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ≫
              Z.windowToCycles (k + 1) (a + b - r) r hr ≫
                Z.windowπ (k + 1) (a + b - r) r r hr hr := by
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc, Category.comp_id, representatives_windowD]
  have ht :
      ((X.intervalδ n (n + 1) (a - r - r) (a - r) a (by omega) (by omega) rfl ≫
        (X.windowToCycles (n + 1) (a - r) r hr ≫ X.windowπ (n + 1) (a - r) r r hr hr)) ⊗ₘ
        (Y.windowToCycles m b r hr ≫ Y.windowπ m b r r hr hr)) =
      (X.intervalδ n (n + 1) (a - r - r) (a - r) a (by omega) (by omega) rfl ⊗ₘ 𝟙 _) ≫
        ((X.windowToCycles (n + 1) (a - r) r hr ≫ X.windowπ (n + 1) (a - r) r r hr hr) ⊗ₘ
          (Y.windowToCycles m b r hr ≫ Y.windowπ m b r r hr hr)) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  rw [ht, Category.assoc, P.representatives_windowPairTo (n + 1) m (k + 1)
    (by omega) (a - r) b (a + b - r) (by omega) r r hr hr le_rfl]

@[reassoc]
lemma representatives_right_differential_product (n m k : ℤ) (hnm : n + m = k)
    (a b r : ℤ) (hr : 1 ≤ r) :
    ((X.windowToCycles n a r hr ≫ X.windowπ n a r r hr hr) ⊗ₘ
      (Y.windowToCycles m b r hr ≫ Y.windowπ m b r r hr hr)) ≫
      (𝟙 _ ⊗ₘ Y.windowD m b r hr) ≫
        P.windowPairTo n (m + 1) (k + 1) (by omega) a (b - r) (a + b - r)
          (by omega) r r hr hr le_rfl =
      (𝟙 (X.intervalH n (a - r) a (by omega)) ⊗ₘ
        Y.intervalδ m (m + 1) (b - r - r) (b - r) b (by omega) (by omega) rfl) ≫
          P.pair n (m + 1) (k + 1) (a - r) a (b - r - r) (b - r)
            (a + b - r - r) (a + b - r) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ≫
              Z.windowToCycles (k + 1) (a + b - r) r hr ≫
                Z.windowπ (k + 1) (a + b - r) r r hr hr := by
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc, Category.comp_id, representatives_windowD]
  have ht :
      ((X.windowToCycles n a r hr ≫ X.windowπ n a r r hr hr) ⊗ₘ
        (Y.intervalδ m (m + 1) (b - r - r) (b - r) b (by omega) (by omega) rfl ≫
          (Y.windowToCycles (m + 1) (b - r) r hr ≫ Y.windowπ (m + 1) (b - r) r r hr hr))) =
      (𝟙 _ ⊗ₘ Y.intervalδ m (m + 1) (b - r - r) (b - r) b (by omega) (by omega) rfl) ≫
        ((X.windowToCycles n a r hr ≫ X.windowπ n a r r hr hr) ⊗ₘ
          (Y.windowToCycles (m + 1) (b - r) r hr ≫ Y.windowπ (m + 1) (b - r) r r hr hr)) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  rw [ht, Category.assoc, P.representatives_windowPairTo n (m + 1) (k + 1)
    (by omega) a (b - r) (a + b - r) (by omega) r r hr hr le_rfl]

/-- Cycle products commute with the actual lower-window restriction maps. -/
@[reassoc]
lemma cyclesPair_map (n m k : ℤ) (hnm : n + m = k) (a b ℓ ℓ' : ℤ)
    (hℓ : 1 ≤ ℓ) (hℓ' : 1 ≤ ℓ') (h : ℓ' ≤ ℓ) :
    (X.windowCyclesMap n a ℓ ℓ' hℓ hℓ' h ⊗ₘ
      Y.windowCyclesMap m b ℓ ℓ' hℓ hℓ' h) ≫ P.cyclesPair n m k hnm a b ℓ' hℓ' =
      P.cyclesPair n m k hnm a b ℓ hℓ ≫ Z.windowCyclesMap k (a + b) ℓ ℓ' hℓ hℓ' h := by
  rw [← cancel_mono (Z.windowICycles k (a + b) ℓ' hℓ')]
  simp only [Category.assoc, cyclesPair_i, windowCyclesMap_i]
  rw [← Category.assoc, tensorHom_comp_tensorHom, windowCyclesMap_i, windowCyclesMap_i]

/-- Products commute with native quotient maps under both outer-cut changes. -/
@[reassoc]
lemma windowPair_map (n m k : ℤ) (hnm : n + m = k) (a b ℓ u ℓ' u' : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (hℓ' : 1 ≤ ℓ') (hu' : 1 ≤ u')
    (huℓ : u ≤ ℓ) (hu'ℓ' : u' ≤ ℓ') (hℓ'ℓ : ℓ' ≤ ℓ) (huu' : u ≤ u') :
    (X.windowMap n a ℓ u ℓ' u' hℓ hu hℓ' hu' hℓ'ℓ huu' ⊗ₘ
      Y.windowMap m b ℓ u ℓ' u' hℓ hu hℓ' hu' hℓ'ℓ huu') ≫
        P.windowPair n m k hnm a b ℓ' u' hℓ' hu' hu'ℓ' =
      P.windowPair n m k hnm a b ℓ u hℓ hu huℓ ≫
        Z.windowMap k (a + b) ℓ u ℓ' u' hℓ hu hℓ' hu' hℓ'ℓ huu' := by
  letI : Epi (X.windowπ n a ℓ u hℓ hu ⊗ₘ Y.windowπ m b ℓ u hℓ hu) :=
    epi_tensorHom_of_cokernels _ _
  rw [← cancel_epi (X.windowπ n a ℓ u hℓ hu ⊗ₘ Y.windowπ m b ℓ u hℓ hu)]
  rw [← Category.assoc, tensorHom_comp_tensorHom, windowπ_map, windowπ_map,
    ← tensorHom_comp_tensorHom_assoc, quotient_windowPair]
  rw [quotient_windowPair_assoc, windowπ_map]
  rw [← Category.assoc, P.cyclesPair_map n m k hnm a b ℓ ℓ' hℓ hℓ' hℓ'ℓ,
    Category.assoc]

/-- Signed Leibniz for the actual spectral-object differential, derived from
aligned original triple boundaries and quotient descent. -/
lemma windowPair_leibniz (n m k : ℤ) (hnm : n + m = k) (a b r : ℤ) (hr : 1 ≤ r) :
    P.windowPair n m k hnm a b r r hr hr le_rfl ≫ Z.windowD k (a + b) r hr =
      (X.windowD n a r hr ⊗ₘ 𝟙 _) ≫
        P.windowPairTo (n + 1) m (k + 1) (by omega) (a - r) b (a + b - r)
          (by omega) r r hr hr le_rfl +
      (n.negOnePow : ℤ) •
        ((𝟙 _ ⊗ₘ Y.windowD m b r hr) ≫
          P.windowPairTo n (m + 1) (k + 1) (by omega) a (b - r) (a + b - r)
            (by omega) r r hr hr le_rfl) := by
  subst k
  letI : Epi ((X.windowToCycles n a r hr ≫ X.windowπ n a r r hr hr) ⊗ₘ
      (Y.windowToCycles m b r hr ≫ Y.windowπ m b r r hr hr)) :=
    epi_tensorHom_of_cokernels _ _
  rw [← cancel_epi ((X.windowToCycles n a r hr ≫ X.windowπ n a r r hr hr) ⊗ₘ
    (Y.windowToCycles m b r hr ≫ Y.windowπ m b r r hr hr))]
  simp only [Preadditive.comp_add, Preadditive.comp_zsmul]
  rw [P.representatives_windowPair_assoc n m (n + m) rfl a b r r hr hr le_rfl,
    representatives_windowD, P.representatives_left_differential_product n m (n + m)
      rfl a b r hr, P.representatives_right_differential_product n m (n + m) rfl a b r hr]
  dsimp only [longPair]
  rw [← Category.assoc, P.boundary_aligned n m a b r hr]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc]

/-- Native quotient maps commute with a product at any explicitly chosen sum cut. -/
@[reassoc]
lemma windowPairTo_map (n m k : ℤ) (hnm : n + m = k) (a b s : ℤ) (hs : a + b = s)
    (ℓ u ℓ' u' : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (hℓ' : 1 ≤ ℓ') (hu' : 1 ≤ u')
    (huℓ : u ≤ ℓ) (hu'ℓ' : u' ≤ ℓ') (hℓ'ℓ : ℓ' ≤ ℓ) (huu' : u ≤ u') :
    (X.windowMap n a ℓ u ℓ' u' hℓ hu hℓ' hu' hℓ'ℓ huu' ⊗ₘ
      Y.windowMap m b ℓ u ℓ' u' hℓ hu hℓ' hu' hℓ'ℓ huu') ≫
        P.windowPairTo n m k hnm a b s hs ℓ' u' hℓ' hu' hu'ℓ' =
      P.windowPairTo n m k hnm a b s hs ℓ u hℓ hu huℓ ≫
        Z.windowMap k s ℓ u ℓ' u' hℓ hu hℓ' hu' hℓ'ℓ huu' := by
  subst s
  exact P.windowPair_map n m k hnm a b ℓ u ℓ' u' hℓ hu hℓ' hu' huℓ hu'ℓ' hℓ'ℓ huu'

/-- The constructed product on the original native spectral-sequence page. -/
def pagePair (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).X pq ⊗
      ((Y.skeletalSpectralSequence).page r).X pq' ⟶
        ((Z.skeletalSpectralSequence).page r).X (pq + pq') :=
  ((X.pageWindowIso r hr pq).hom ⊗ₘ (Y.pageWindowIso r hr pq').hom) ≫
    P.windowPairTo (pq.1 + pq.2) (pq'.1 + pq'.2) ((pq + pq').1 + (pq + pq').2)
      (by dsimp; omega) (-pq.1) (-pq'.1) (-(pq + pq').1) (by dsimp; omega)
      r r hr hr le_rfl ≫ (Z.pageWindowIso r hr (pq + pq')).inv

/-- The constructed page product with an explicitly equal sum position. -/
def pagePairTo (r : ℤ) (hr : 1 ≤ r) (pq pq' t : ℤ × ℤ) (ht : pq + pq' = t) :
    ((X.skeletalSpectralSequence).page r).X pq ⊗
      ((Y.skeletalSpectralSequence).page r).X pq' ⟶
        ((Z.skeletalSpectralSequence).page r).X t := by
  subst t
  exact P.pagePair r hr pq pq'

@[reassoc]
lemma pagePairTo_window (r : ℤ) (hr : 1 ≤ r) (pq pq' t : ℤ × ℤ) (ht : pq + pq' = t)
    (n m k a b s : ℤ) (hn : n = pq.1 + pq.2) (hm : m = pq'.1 + pq'.2)
    (hk : k = t.1 + t.2) (ha : a = -pq.1) (hb : b = -pq'.1) (hs : s = -t.1)
    (hnm : n + m = k) (hab : a + b = s) :
    ((X.pageWindowIsoAt r hr pq n a hn ha).inv ⊗ₘ
      (Y.pageWindowIsoAt r hr pq' m b hm hb).inv) ≫ P.pagePairTo r hr pq pq' t ht ≫
        (Z.pageWindowIsoAt r hr t k s hk hs).hom =
      P.windowPairTo n m k hnm a b s hab r r hr hr le_rfl := by
  subst t n m k a b s
  dsimp only [pagePairTo, pagePair, pageWindowIsoAt]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Iso.inv_hom_id, tensorHom_id, id_whiskerRight, Category.id_comp,
    Category.assoc, Category.comp_id]

@[reassoc]
lemma pagePairTo_window_inv (r : ℤ) (hr : 1 ≤ r) (pq pq' t : ℤ × ℤ) (ht : pq + pq' = t)
    (n m k a b s : ℤ) (hn : n = pq.1 + pq.2) (hm : m = pq'.1 + pq'.2)
    (hk : k = t.1 + t.2) (ha : a = -pq.1) (hb : b = -pq'.1) (hs : s = -t.1)
    (hnm : n + m = k) (hab : a + b = s) :
    ((X.pageWindowIsoAt r hr pq n a hn ha).inv ⊗ₘ
      (Y.pageWindowIsoAt r hr pq' m b hm hb).inv) ≫ P.pagePairTo r hr pq pq' t ht =
      P.windowPairTo n m k hnm a b s hab r r hr hr le_rfl ≫
        (Z.pageWindowIsoAt r hr t k s hk hs).inv := by
  rw [← cancel_mono (Z.pageWindowIsoAt r hr t k s hk hs).hom,
    Category.assoc, P.pagePairTo_window r hr pq pq' t ht n m k a b s hn hm hk ha hb hs hnm hab]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The constructed product on actual native page cycles, using the genuine
asymmetric cycle windows supplied by native homology data. -/
def pageCyclesPair (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).cycles pq ⊗
      ((Y.skeletalSpectralSequence).page r).cycles pq' ⟶
        ((Z.skeletalSpectralSequence).page r).cycles (pq + pq') :=
  ((X.pageCyclesWindowIso r hr pq).hom ⊗ₘ (Y.pageCyclesWindowIso r hr pq').hom) ≫
    P.windowPairTo (pq.1 + pq.2) (pq'.1 + pq'.2) ((pq + pq').1 + (pq + pq').2)
      (by dsimp; omega) (-pq.1) (-pq'.1) (-(pq + pq').1) (by dsimp; omega)
      (r + 1) r (by omega) hr (by omega) ≫ (Z.pageCyclesWindowIso r hr (pq + pq')).inv

/-- The candidate homology product, independently constructed from the enlarged
symmetric interval window. Its quotient formula is proved below. -/
def pageHomologyWindowPair (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).homology pq ⊗
      ((Y.skeletalSpectralSequence).page r).homology pq' ⟶
        ((Z.skeletalSpectralSequence).page r).homology (pq + pq') :=
  ((X.pageHomologyWindowIso r hr pq).hom ⊗ₘ (Y.pageHomologyWindowIso r hr pq').hom) ≫
    P.windowPairTo (pq.1 + pq.2) (pq'.1 + pq'.2) ((pq + pq').1 + (pq + pq').2)
      (by dsimp; omega) (-pq.1) (-pq'.1) (-(pq + pq').1) (by dsimp; omega)
      (r + 1) (r + 1) (by omega) (by omega) le_rfl ≫
        (Z.pageHomologyWindowIso r hr (pq + pq')).inv

/-- The interval-cycle product is the actual product on cycles of the native page. -/
@[reassoc]
lemma pageCyclesPair_i (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    P.pageCyclesPair r hr pq pq' ≫ ((Z.skeletalSpectralSequence).page r).iCycles (pq + pq') =
      (((X.skeletalSpectralSequence).page r).iCycles pq ⊗ₘ
        ((Y.skeletalSpectralSequence).page r).iCycles pq') ≫ P.pagePair r hr pq pq' := by
  rw [← cancel_mono (Z.pageWindowIso r hr (pq + pq')).hom]
  dsimp only [pageCyclesPair, pagePair]
  simp only [Category.assoc, pageCyclesWindowIso_inv_i, Iso.inv_hom_id, Category.comp_id]
  rw [tensorHom_comp_tensorHom_assoc, pageCyclesWindowIso_i_page,
    pageCyclesWindowIso_i_page, ← tensorHom_comp_tensorHom_assoc]
  rw [P.windowPairTo_map (pq.1 + pq.2) (pq'.1 + pq'.2)
    ((pq + pq').1 + (pq + pq').2) (by dsimp; omega)
    (-pq.1) (-pq'.1) (-(pq + pq').1) (by dsimp; omega)
    (r + 1) r r r (by omega) hr hr hr (by omega) le_rfl (by omega) le_rfl]

/-- The actual homology projections carry the cycle product to the enlarged
interval product. This is the required tensor-to-homology quotient formula. -/
@[reassoc]
lemma pageHomologyWindowPair_π (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    (((X.skeletalSpectralSequence).page r).homologyπ pq ⊗ₘ
      ((Y.skeletalSpectralSequence).page r).homologyπ pq') ≫
        P.pageHomologyWindowPair r hr pq pq' =
      P.pageCyclesPair r hr pq pq' ≫ ((Z.skeletalSpectralSequence).page r).homologyπ (pq + pq') := by
  dsimp only [pageHomologyWindowPair, pageCyclesPair]
  simp only [Category.assoc, pageCyclesWindowIso_inv_π]
  rw [← Category.assoc, tensorHom_comp_tensorHom, pageHomologyWindowIso_π,
    pageHomologyWindowIso_π, ← tensorHom_comp_tensorHom_assoc]
  rw [P.windowPairTo_map_assoc (pq.1 + pq.2) (pq'.1 + pq'.2)
    ((pq + pq').1 + (pq + pq').2) (by dsimp; omega)
    (-pq.1) (-pq'.1) (-(pq + pq').1) (by dsimp; omega)
    (r + 1) r (r + 1) (r + 1) (by omega) hr (by omega) (by omega)
      (by omega) le_rfl le_rfl (by omega)]

/-- Both actual native page boundary relations vanish after the constructed
cycle product and homology projection. -/
lemma pageCyclesPair_boundaries_zero (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    coprod.desc
      (((X.skeletalSpectralSequence).page r).toCycles
        ((ComplexShape.up' (r, 1 - r)).prev pq) pq ▷
          ((Y.skeletalSpectralSequence).page r).cycles pq')
      (((X.skeletalSpectralSequence).page r).cycles pq ◁
        ((Y.skeletalSpectralSequence).page r).toCycles
          ((ComplexShape.up' (r, 1 - r)).prev pq') pq') ≫
      (P.pageCyclesPair r hr pq pq' ≫
        ((Z.skeletalSpectralSequence).page r).homologyπ (pq + pq')) = 0 := by
  rw [← P.pageHomologyWindowPair_π r hr pq pq']
  apply coprod.hom_ext
  · simp [tensorHom_def, ← comp_whiskerRight_assoc]
  · simp [tensorHom_def', ← whiskerLeft_comp_assoc]

/-- The tensor-to-homology product descended through the actual native cycle
and boundary cokernel presentations. -/
def pageHomologyPair (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).homology pq ⊗
      ((Y.skeletalSpectralSequence).page r).homology pq' ⟶
        ((Z.skeletalSpectralSequence).page r).homology (pq + pq') :=
  HomologicalComplex.tensorHomologyDesc
    ((X.skeletalSpectralSequence).page r) ((ComplexShape.up' (r, 1 - r)).prev pq) pq rfl
    ((Y.skeletalSpectralSequence).page r) ((ComplexShape.up' (r, 1 - r)).prev pq') pq' rfl
    (P.pageCyclesPair r hr pq pq' ≫ ((Z.skeletalSpectralSequence).page r).homologyπ (pq + pq'))
    (P.pageCyclesPair_boundaries_zero r hr pq pq')

@[reassoc (attr := simp)]
lemma pageHomologyPair_π (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    (((X.skeletalSpectralSequence).page r).homologyπ pq ⊗ₘ
      ((Y.skeletalSpectralSequence).page r).homologyπ pq') ≫ P.pageHomologyPair r hr pq pq' =
      P.pageCyclesPair r hr pq pq' ≫ ((Z.skeletalSpectralSequence).page r).homologyπ (pq + pq') :=
  HomologicalComplex.tensor_homologyπ_comp_tensorHomologyDesc
    ((X.skeletalSpectralSequence).page r) ((ComplexShape.up' (r, 1 - r)).prev pq) pq rfl
    ((Y.skeletalSpectralSequence).page r) ((ComplexShape.up' (r, 1 - r)).prev pq') pq' rfl
    (P.pageCyclesPair r hr pq pq' ≫ ((Z.skeletalSpectralSequence).page r).homologyπ (pq + pq'))
    (P.pageCyclesPair_boundaries_zero r hr pq pq')

/-- Native quotient descent agrees with the independently constructed enlarged
interval product; this is an equality of maps, not a tensor-homology isomorphism. -/
lemma pageHomologyPair_eq_windowPair (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    P.pageHomologyPair r hr pq pq' = P.pageHomologyWindowPair r hr pq pq' := by
  apply HomologicalComplex.tensor_homologyπ_hom_ext
    ((X.skeletalSpectralSequence).page r) ((ComplexShape.up' (r, 1 - r)).prev pq) pq rfl
    ((Y.skeletalSpectralSequence).page r) ((ComplexShape.up' (r, 1 - r)).prev pq') pq' rfl
  rw [P.pageHomologyPair_π r hr pq pq', P.pageHomologyWindowPair_π r hr pq pq']

/-- The product induced on actual page homology is carried by the native
successor isomorphisms to the constructed product on the next page. -/
lemma pagePair_successor (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    P.pageHomologyPair r hr pq pq' ≫
        ((Z.skeletalSpectralSequence).iso r (r + 1) (pq + pq') rfl hr).hom =
      (((X.skeletalSpectralSequence).iso r (r + 1) pq rfl hr).hom ⊗ₘ
        ((Y.skeletalSpectralSequence).iso r (r + 1) pq' rfl hr).hom) ≫
          P.pagePair (r + 1) (by omega) pq pq' := by
  rw [P.pageHomologyPair_eq_windowPair r hr pq pq',
    ← cancel_mono (Z.pageWindowIso (r + 1) (by omega) (pq + pq')).hom]
  rw [Category.assoc, pageHomologyWindowIso_successor]
  dsimp only [pageHomologyWindowPair, pagePair]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [tensorHom_comp_tensorHom_assoc, pageHomologyWindowIso_successor,
    pageHomologyWindowIso_successor]

/-- The signed Leibniz identity for the original native `d_r`, of bidegree
`(r, 1-r)`. Both bidegree coordinates and the sign degree range over all integers. -/
lemma pagePair_leibniz (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    P.pagePair r hr pq pq' ≫
        ((Z.skeletalSpectralSequence).page r).d (pq + pq') ((pq + pq') + (r, 1 - r)) =
      (((X.skeletalSpectralSequence).page r).d pq (pq + (r, 1 - r)) ⊗ₘ 𝟙 _) ≫
        P.pagePairTo r hr (pq + (r, 1 - r)) pq' ((pq + pq') + (r, 1 - r))
          (by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega) +
      ((pq.1 + pq.2).negOnePow : ℤ) •
        ((𝟙 _ ⊗ₘ ((Y.skeletalSpectralSequence).page r).d pq' (pq' + (r, 1 - r))) ≫
          P.pagePairTo r hr pq (pq' + (r, 1 - r)) ((pq + pq') + (r, 1 - r))
            (by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega)) := by
  let n := pq.1 + pq.2
  let m := pq'.1 + pq'.2
  let a := -pq.1
  let b := -pq'.1
  let t := (pq + pq') + (r, 1 - r)
  have ht₁ : t.1 = pq.1 + pq'.1 + r := rfl
  have ht₂ : t.2 = pq.2 + pq'.2 + (1 - r) := rfl
  let eX := X.pageWindowIsoAt r hr pq n a rfl rfl
  let eY := Y.pageWindowIsoAt r hr pq' m b rfl rfl
  let eS := Z.pageWindowIsoAt r hr (pq + pq') (n + m) (a + b)
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
  let eT := Z.pageWindowIsoAt r hr t (n + m + 1) (a + b - r)
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
  let eDX := X.pageWindowIsoAt r hr (pq + (r, 1 - r)) (n + 1) (a - r)
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
  let eDY := Y.pageWindowIsoAt r hr (pq' + (r, 1 - r)) (m + 1) (b - r)
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
  let dX := ((X.skeletalSpectralSequence).page r).d pq (pq + (r, 1 - r))
  let dY := ((Y.skeletalSpectralSequence).page r).d pq' (pq' + (r, 1 - r))
  let dZ := ((Z.skeletalSpectralSequence).page r).d (pq + pq') t
  let pL := P.pagePairTo r hr (pq + (r, 1 - r)) pq' t (by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega)
  let pR := P.pagePairTo r hr pq (pq' + (r, 1 - r)) t (by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega)
  have hP := P.pagePairTo_window_inv r hr pq pq' (pq + pq') rfl n m (n + m) a b (a + b)
    rfl rfl (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega)) rfl rfl
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega)) rfl rfl
  change (eX.inv ⊗ₘ eY.inv) ≫ P.pagePair r hr pq pq' =
    P.windowPair n m (n + m) rfl a b r r hr hr le_rfl ≫ eS.inv at hP
  have hdX := X.pageWindowIsoAt_inv_d r hr pq n a rfl rfl
  change eX.inv ≫ dX = X.windowD n a r hr ≫ eDX.inv at hdX
  have hdY := Y.pageWindowIsoAt_inv_d r hr pq' m b rfl rfl
  change eY.inv ≫ dY = Y.windowD m b r hr ≫ eDY.inv at hdY
  have hdZ := Z.pageWindowIsoAt_inv_d r hr (pq + pq') (n + m) (a + b)
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
  change eS.inv ≫ dZ = Z.windowD (n + m) (a + b) r hr ≫ eT.inv at hdZ
  have hpL := P.pagePairTo_window r hr (pq + (r, 1 - r)) pq' t
    (by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega) (n + 1) m (n + m + 1) (a - r) b (a + b - r)
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega)) rfl
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega)) rfl
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
  change (eDX.inv ⊗ₘ eY.inv) ≫ pL ≫ eT.hom =
    P.windowPairTo (n + 1) m (n + m + 1) (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
      (a - r) b (a + b - r)
      (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega)) r r hr hr le_rfl at hpL
  have hpR := P.pagePairTo_window r hr pq (pq' + (r, 1 - r)) t
    (by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega) n (m + 1) (n + m + 1) a (b - r) (a + b - r)
    rfl (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega)) rfl
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
    (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
  change (eX.inv ⊗ₘ eDY.inv) ≫ pR ≫ eT.hom =
    P.windowPairTo n (m + 1) (n + m + 1) (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
      a (b - r) (a + b - r)
      (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega)) r r hr hr le_rfl at hpR
  have hLpre : (eX.inv ⊗ₘ eY.inv) ≫ (dX ⊗ₘ 𝟙 _) =
      (X.windowD n a r hr ⊗ₘ 𝟙 _) ≫ (eDX.inv ⊗ₘ eY.inv) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.comp_id, hdX]
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  have hRpre : (eX.inv ⊗ₘ eY.inv) ≫ (𝟙 _ ⊗ₘ dY) =
      (𝟙 _ ⊗ₘ Y.windowD m b r hr) ≫ (eX.inv ⊗ₘ eDY.inv) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.comp_id, hdY]
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  have hS : (eX.inv ⊗ₘ eY.inv) ≫ P.pagePair r hr pq pq' ≫ dZ ≫ eT.hom =
      P.windowPair n m (n + m) rfl a b r r hr hr le_rfl ≫ Z.windowD (n + m) (a + b) r hr := by
    rw [← Category.assoc (eX.inv ⊗ₘ eY.inv) (P.pagePair r hr pq pq') (dZ ≫ eT.hom), hP]
    rw [Category.assoc, ← Category.assoc eS.inv dZ eT.hom, hdZ]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hL : (eX.inv ⊗ₘ eY.inv) ≫ (dX ⊗ₘ 𝟙 _) ≫ pL ≫ eT.hom =
      (X.windowD n a r hr ⊗ₘ 𝟙 _) ≫
        P.windowPairTo (n + 1) m (n + m + 1) (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
          (a - r) b (a + b - r)
          (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega)) r r hr hr le_rfl := by
    rw [← Category.assoc (eX.inv ⊗ₘ eY.inv) (dX ⊗ₘ 𝟙 _) (pL ≫ eT.hom), hLpre,
      Category.assoc, hpL]
  have hR : (eX.inv ⊗ₘ eY.inv) ≫ (𝟙 _ ⊗ₘ dY) ≫ pR ≫ eT.hom =
      (𝟙 _ ⊗ₘ Y.windowD m b r hr) ≫
        P.windowPairTo n (m + 1) (n + m + 1) (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega))
          a (b - r) (a + b - r)
          (by first | omega | (simp only [Prod.fst_add, Prod.snd_add]; omega)) r r hr hr le_rfl := by
    rw [← Category.assoc (eX.inv ⊗ₘ eY.inv) (𝟙 _ ⊗ₘ dY) (pR ≫ eT.hom), hRpre,
      Category.assoc, hpR]
  rw [← cancel_epi (eX.inv ⊗ₘ eY.inv), ← cancel_mono eT.hom]
  change ((eX.inv ⊗ₘ eY.inv) ≫ (P.pagePair r hr pq pq' ≫ dZ)) ≫ eT.hom =
    ((eX.inv ⊗ₘ eY.inv) ≫ ((dX ⊗ₘ 𝟙 _) ≫ pL + (n.negOnePow : ℤ) • ((𝟙 _ ⊗ₘ dY) ≫ pR))) ≫ eT.hom
  simp only [Preadditive.comp_add, Preadditive.comp_zsmul, Preadditive.add_comp,
    Preadditive.zsmul_comp, Category.assoc]
  rw [hS, hL, hR]
  exact P.windowPair_leibniz n m (n + m) rfl a b r hr

end IntervalPairing

end CategoryTheory.Abelian.SpectralObject
