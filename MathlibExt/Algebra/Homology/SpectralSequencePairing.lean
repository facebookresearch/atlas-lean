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
# Interval products and spectral-page pairings

For a spectral object over EInt, write H_n(a,b) for interval cohomology. The window with cuts
a−ℓ,a−1,a,a+u−1 gives a cycle object and its boundary quotient. On the skeletal page at (p,q),
its total degree is p+q and cut is −p; page r uses widths (r,r), page cycles use (r+1,r), and
page homology uses (r+1,r+1).

An interval pairing records natural products H_n(a,b) ⊗ H_m(c,d) → H_{n+m}(s,t) with a+d≤s,
b+c≤s and b+d≤t. Its boundary rules have first-factor sign 1 and second-factor sign (−1)^n.
With left and right tensoring preserving coequalizers, these products lift to cycles and
descend to window quotients for 1≤u≤ℓ.

The resulting page products have additive bidegree, commute with the successor homology
comparisons, and satisfy the Leibniz rule with sign (−1)^{p+q} on the second differential
term. The boundary quotient universal properties define these products.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type*} [Category* C] [Abelian C]

/-- The cohomology object of an integer interval.

Evaluate H_n of the spectral object on the interval a→b, with a≤b. -/
abbrev intervalH (X : SpectralObject C EInt) (n a b : ℤ) (hab : a ≤ b) : C :=
  (X.H n).obj (mk₁ (homOfLE (show (a : EInt) ≤ (b : EInt) by simpa using hab)))

/-- The map between ordered integer intervals.

For increasing lower and upper endpoints, use the induced H_n map of interval arrows. -/
def intervalMap (X : SpectralObject C EInt) (n a b a' b' : ℤ)
    (hab : a ≤ b) (hab' : a' ≤ b') (ha : a ≤ a') (hb : b ≤ b') :
    X.intervalH n a b hab ⟶ X.intervalH n a' b' hab' :=
  (X.H n).map (homMk₁
    (homOfLE (show (a : EInt) ≤ (a' : EInt) by simpa using ha))
    (homOfLE (show (b : EInt) ≤ (b' : EInt) by simpa using hb)) (by cat_disch))

/-- The identity map of an integer interval.

Keeping both endpoints fixed gives the identity interval map. -/
@[simp]
lemma intervalMap_id (X : SpectralObject C EInt) (n a b : ℤ) (hab : a ≤ b) :
    X.intervalMap n a b a b hab hab le_rfl le_rfl = 𝟙 _ := by
  change (X.H n).map _ = _
  convert CategoryTheory.Functor.map_id (X.H n) _ using 1
  congr 1

/-- Composition of integer interval maps.

Two successive endpoint maps compose to the direct interval map. -/
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

/-- The triple-interval boundary map.

For a≤b≤c, the boundary sends H_n(b,c) to H_{n+1}(a,b). -/
abbrev intervalδ (X : SpectralObject C EInt) (n n' a b c : ℤ)
    (hab : a ≤ b) (hbc : b ≤ c) (hn : n + 1 = n') :
    X.intervalH n b c hbc ⟶ X.intervalH n' a b hab :=
  X.δ (homOfLE (show (a : EInt) ≤ (b : EInt) by simpa using hab))
    (homOfLE (show (b : EInt) ≤ (c : EInt) by simpa using hbc)) n n' hn

/-- The cycle object of a lower-width window.

For ℓ≥1, take cycles associated to a−ℓ→a−1→a in degree n. -/
abbrev windowCycles (X : SpectralObject C EInt) (n a ℓ : ℤ) (hℓ : 1 ≤ ℓ) : C :=
  X.cycles (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by
    simp; omega)) (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp)) n

/-- The boundary quotient of an integer window.

For ℓ,u≥1, use the cuts a−ℓ,a−1,a,a+u−1 and neighboring degrees n−1,n,n+1. -/
abbrev windowE (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) : C :=
  X.E (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by
    simp; omega)) (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp))
    (homOfLE (show (a : EInt) ≤ ((a + u - 1 : ℤ) : EInt) by simp; omega))
    (n - 1) n (n + 1)

/-- The long-interval map into window cycles.

Map H_n(a−ℓ,a) into the cycles of the lower-width window. -/
abbrev windowToCycles (X : SpectralObject C EInt) (n a ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.intervalH n (a - ℓ) a (by omega) ⟶ X.windowCycles n a ℓ hℓ :=
  X.toCycles _ _ (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ (a : EInt) by simp; omega))
    (by cat_disch) n

/-- The inclusion of window cycles into the short interval.

Include the window cycles into H_n(a−1,a). -/
abbrev windowICycles (X : SpectralObject C EInt) (n a ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.windowCycles n a ℓ hℓ ⟶ X.intervalH n (a - 1) a (by omega) :=
  X.iCycles _ _ n

/-- The window cycles-to-boundary-quotient projection.

Project the lower-width cycle object to the window E object with upper width u. -/
abbrev windowπ (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    X.windowCycles n a ℓ hℓ ⟶ X.windowE n a ℓ u hℓ hu :=
  X.πE _ _ _ (n - 1) n (n + 1)

/-- The incoming boundary map of a window.

Map H_{n−1}(a,a+u−1) into the lower-width cycle object in degree n. -/
abbrev windowBoundary (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    X.intervalH (n - 1) a (a + u - 1) (by omega) ⟶ X.windowCycles n a ℓ hℓ :=
  X.δToCycles _ _ _ (n - 1) n

/-- The long-interval cycle map preserves its short restriction.

The map into cycles followed by inclusion equals the interval map from a−ℓ→a to a−1→a. -/
@[reassoc]
lemma windowToCycles_i (X : SpectralObject C EInt) (n a ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.windowToCycles n a ℓ hℓ ≫ X.windowICycles n a ℓ hℓ =
      X.intervalMap n (a - ℓ) a (a - 1) a (by omega) (by omega) (by omega) le_rfl := by
  rw [toCycles_i]
  congr 1

/-- The window boundary preserves the triple boundary coordinate.

The incoming boundary followed by cycle inclusion is the triple-interval boundary into
H_n(a−1,a). -/
@[reassoc]
lemma windowBoundary_i (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    X.windowBoundary n a ℓ u hℓ hu ≫ X.windowICycles n a ℓ hℓ =
      X.intervalδ (n - 1) n (a - 1) a (a + u - 1) (by omega) (by omega) (by omega) := by
  apply δToCycles_iCycles

/-- The window boundary is killed by its quotient projection.

The composite of the incoming boundary with the window projection is zero. -/
@[reassoc]
lemma windowBoundary_π (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    X.windowBoundary n a ℓ u hℓ hu ≫ X.windowπ n a ℓ u hℓ hu = 0 := by
  apply δToCycles_πE

/-- The cokernel cofork defining a window quotient.

The cycle projection and its boundary-zero relation form the cofork of the incoming boundary. -/
def windowCofork (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    CokernelCofork (X.windowBoundary n a ℓ u hℓ hu) :=
  CokernelCofork.ofπ (X.windowπ n a ℓ u hℓ hu) (X.windowBoundary_π n a ℓ u hℓ hu)

/-- The window projection has the boundary cokernel universal property.

The window E object is the cokernel of the incoming boundary into cycles. -/
def windowCoforkIsColimit (X : SpectralObject C EInt) (n a ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) : IsColimit (X.windowCofork n a ℓ u hℓ hu) :=
  (X.cokernelSequenceCyclesE_exact _ _ _ (n - 1) n (n + 1)).gIsCokernel

/-- The cycle map for a smaller lower width.

For ℓ′≤ℓ, map cycles from width ℓ to width ℓ′ with the same short interval. -/
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

/-- Changing lower width preserves cycle inclusion.

The lower-width cycle map followed by the target inclusion equals the source inclusion. -/
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

/-- The map between nested window quotients.

For ℓ′≤ℓ and u≤u′, map the source window quotient to the target with those widths. -/
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

/-- Window maps commute with cycle projection.

The source projection followed by the window map equals the cycle-width map followed by the
target projection. -/
@[reassoc (attr := simp)]
lemma windowπ_map (X : SpectralObject C EInt) (n a ℓ u ℓ' u' : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (hℓ' : 1 ≤ ℓ') (hu' : 1 ≤ u')
    (hℓ'ℓ : ℓ' ≤ ℓ) (huu' : u ≤ u') :
    X.windowπ n a ℓ u hℓ hu ≫ X.windowMap n a ℓ u ℓ' u' hℓ hu hℓ' hu' hℓ'ℓ huu' =
      X.windowCyclesMap n a ℓ ℓ' hℓ hℓ' hℓ'ℓ ≫ X.windowπ n a ℓ' u' hℓ' hu' := by
  dsimp only [windowMap, windowCyclesMap]
  exact X.πE_map _ _ _ _ _ _ _ _ (n - 1) n (n + 1) (by cat_disch) (by omega) rfl

/-- The equality comparison of a window output presentation.

Normalize neighboring degrees to n−1,n,n+1 and the final cut to a+u−1 to obtain the standard
window E object. -/
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

/-- The normalized output comparison preserves the window projection.

The E projection followed by the output isomorphism equals the standard window projection. -/
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

/-- The boundary-induced differential of an equal-width window.

For r≥1, map the (r,r)-window at (n,a) to that at (n+1,a−r) using the spectral-object
boundary. -/
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

/-- The window differential on long-interval representatives.

The long interval representative followed by the window differential equals the triple
boundary followed by the target representative. -/
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

/-- The skeletal page object identified with an interval window.

At (p,q), page r is the (r,r)-window of total degree p+q and cut −p. -/
def pageWindowIso (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).X pq ≅
      X.windowE (pq.1 + pq.2) (-pq.1) r r hr hr :=
  X.spectralSequencePageXIso skeletalPageCore r hr pq
    (-pq.1 - r : ℤ) (-pq.1 - 1 : ℤ) (-pq.1 : ℤ) (-pq.1 + r - 1 : ℤ)
    rfl rfl rfl rfl (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) rfl

/-- The page-window comparison with specified degree and cut.

For n=p+q and a=−p, identify the page object with the window in those coordinates. -/
def pageWindowIsoAt (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ)
    (n a : ℤ) (hn : n = pq.1 + pq.2) (ha : a = -pq.1) :
    ((X.skeletalSpectralSequence).page r).X pq ≅ X.windowE n a r r hr hr := by
  subst n a
  exact X.pageWindowIso r hr pq

/-- The specified page chart agrees with output normalization.

Normalizing the neighboring degrees and upper cut in the page E presentation gives
pageWindowIsoAt. -/
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

/-- The page differential in interval-window coordinates.

The differential of bidegree (r,1−r), conjugated by the page charts, is windowD from (n,a) to
(n+1,a−r). -/
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

/-- The inverse page chart intertwines the differential.

The inverse source chart followed by the page differential equals windowD followed by the
inverse target chart. -/
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

/-- The window homology data of a skeletal page.

Use the lower-expanded and upper-expanded windows to give the page cycle and homology data for
its successor. -/
def pageWindowHomologyData (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) : (((X.skeletalSpectralSequence).page r).sc pq).HomologyData :=
  X.spectralSequenceHomologyData skeletalPageCore r (r + 1) rfl hr
    ((ComplexShape.up' (r, 1 - r)).prev pq) pq
    ((ComplexShape.up' (r, 1 - r)).next pq) rfl rfl
    (-pq.1 - (r + 1) : ℤ) (-pq.1 - r : ℤ) (-pq.1 - 1 : ℤ) (-pq.1 : ℤ)
    (-pq.1 + r - 1 : ℤ) (-pq.1 + (r + 1) - 1 : ℤ)
    rfl rfl rfl rfl rfl rfl
    (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) rfl

/-- The cycle object of a page as an expanded window.

Page-r cycles identify with the window of widths (r+1,r) at total degree p+q and cut −p. -/
def pageCyclesWindowIso (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).cycles pq ≅
      X.windowE (pq.1 + pq.2) (-pq.1) (r + 1) r (by omega) hr :=
  (X.pageWindowHomologyData r hr pq).left.cyclesIso

/-- The homology of a page as its successor window.

Page-r homology identifies with the window of widths (r+1,r+1). -/
def pageHomologyWindowIso (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).homology pq ≅
      X.windowE (pq.1 + pq.2) (-pq.1) (r + 1) (r + 1) (by omega) (by omega) :=
  (X.pageWindowHomologyData r hr pq).left.homologyIso

/-- The page cycle window comparison preserves inclusion.

The expanded-window map and inverse page chart recover the page cycle inclusion. -/
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

/-- The page homology window comparison preserves projection.

The page homology projection and chart equal the cycle chart followed by the
expanded-upper-window map. -/
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
/-- The page homology window chart agrees with the successor isomorphism.

The spectral successor followed by its page chart is the page homology window isomorphism. -/
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

/-- The inverse cycle chart preserves the page inclusion.

The inverse expanded-window chart followed by cycle inclusion equals the window restriction
followed by the inverse page chart. -/
@[reassoc]
lemma pageCyclesWindowIso_inv_i (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) :
    (X.pageCyclesWindowIso r hr pq).inv ≫ ((X.skeletalSpectralSequence).page r).iCycles pq =
      X.windowMap (pq.1 + pq.2) (-pq.1) (r + 1) r r r (by omega) hr hr hr
        (by omega) le_rfl ≫ (X.pageWindowIso r hr pq).inv := by
  rw [← X.pageCyclesWindowIso_i r hr pq, Iso.inv_hom_id_assoc]

/-- The page cycle inclusion in its window coordinate.

Cycle inclusion followed by the page chart equals the cycle chart followed by the lower-width
window map. -/
@[reassoc]
lemma pageCyclesWindowIso_i_page (X : SpectralObject C EInt) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).iCycles pq ≫ (X.pageWindowIso r hr pq).hom =
      (X.pageCyclesWindowIso r hr pq).hom ≫
        X.windowMap (pq.1 + pq.2) (-pq.1) (r + 1) r r r (by omega) hr hr hr
          (by omega) le_rfl := by
  rw [← X.pageCyclesWindowIso_i r hr pq]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The inverse cycle chart preserves the homology projection.

The inverse cycle chart followed by homology projection equals the upper-window map followed
by the inverse homology chart. -/
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

/-- Interval products with spectral boundary rules.

For spectral objects X,Y,Z in a monoidal abelian category, record natural interval products
with the filtration endpoint bounds and the first, signed second and aligned boundary
identities. -/
structure IntervalPairing (X Y Z : SpectralObject C EInt) where
  /-- The interval product with compatible filtration cuts.

For n+m=k and intervals (a,b),(c,d),(s,t), pair H_n(a,b) ⊗ H_m(c,d) into H_k(s,t) when a+d≤s,
b+c≤s and b+d≤t. -/
  pair (n m k a b c d s t : ℤ) (hnm : n + m = k)
    (hab : a ≤ b) (hcd : c ≤ d) (hst : s ≤ t)
    (hleft : a + d ≤ s) (hright : b + c ≤ s) (hupper : b + d ≤ t) :
      X.intervalH n a b hab ⊗ Y.intervalH m c d hcd ⟶ Z.intervalH k s t hst
/-- The interval product is natural in all endpoint maps.

Increasing the input and output endpoints under the stated product bounds gives a commuting
tensor-product square. -/
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
/-- The first-factor interval boundary rule.

Applying a boundary in the first factor and restricting the second agrees with pairing first
and then taking the output boundary. -/
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
/-- The signed second-factor interval boundary rule.

The analogous second-factor boundary rule has the integer sign (−1)^n from the first
cohomological degree. -/
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
/-- The aligned interval Leibniz rule.

The output boundary of an aligned product is the first-factor boundary product plus (−1)^n
times the second-factor boundary product. -/
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

/-- The product of two unit-width intervals.

Pair H_n(a−1,a) and H_m(b−1,b) into H_{n+m}(a+b−1,a+b). -/
def shortPair (n m k : ℤ) (hnm : n + m = k) (a b : ℤ) :
    X.intervalH n (a - 1) a (by omega) ⊗ Y.intervalH m (b - 1) b (by omega) ⟶
      Z.intervalH k (a + b - 1) (a + b) (by omega) :=
  P.pair n m k (a - 1) a (b - 1) b (a + b - 1) (a + b)
    hnm (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The product of two equal lower-width intervals.

For ℓ≥1, pair H_n(a−ℓ,a) and H_m(b−ℓ,b) into H_{n+m}(a+b−ℓ,a+b). -/
def longPair (n m k : ℤ) (hnm : n + m = k) (a b ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.intervalH n (a - ℓ) a (by omega) ⊗ Y.intervalH m (b - ℓ) b (by omega) ⟶
      Z.intervalH k (a + b - ℓ) (a + b) (by omega) :=
  P.pair n m k (a - ℓ) a (b - ℓ) b (a + b - ℓ) (a + b)
    hnm (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

-- Keep the original hypothesis parameters and their order in this compatibility declaration.
/-- Long-interval products restrict to short-interval products.

Restricting both inputs and pairing equals pairing the long inputs then restricting the
output. -/
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

/-- The short product of window cycles is an output cycle.

After including both cycle objects, the short interval product is killed by the output
lower-window boundary. -/
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

/-- The induced product on window cycle objects.

Lift the short-interval product of the cycle inclusions into the output cycles. -/
def cyclesPair (n m k : ℤ) (hnm : n + m = k) (a b ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.windowCycles n a ℓ hℓ ⊗ Y.windowCycles m b ℓ hℓ ⟶
      Z.windowCycles k (a + b) ℓ hℓ :=
  Z.liftCycles _ _ k (k + 1) rfl
    ((X.windowICycles n a ℓ hℓ ⊗ₘ Y.windowICycles m b ℓ hℓ) ≫
      P.shortPair n m k hnm a b) (by simpa only [Category.assoc] using P.cyclesPair_boundary_zero n m k hnm a b ℓ hℓ)

/-- The cycle product recovers the included interval product.

Its output inclusion equals the tensor of input inclusions followed by shortPair. -/
@[reassoc (attr := simp)]
lemma cyclesPair_i (n m k : ℤ) (hnm : n + m = k) (a b ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    P.cyclesPair n m k hnm a b ℓ hℓ ≫ Z.windowICycles k (a + b) ℓ hℓ =
      (X.windowICycles n a ℓ hℓ ⊗ₘ Y.windowICycles m b ℓ hℓ) ≫
        P.shortPair n m k hnm a b := by
  apply liftCycles_i

/-- The cycle product on long-interval representatives.

The two maps into cycles followed by cyclesPair equal longPair followed by the output map into
cycles. -/
@[reassoc (attr := simp)]
lemma toCycles_cyclesPair (n m k : ℤ) (hnm : n + m = k) (a b ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    (X.windowToCycles n a ℓ hℓ ⊗ₘ Y.windowToCycles m b ℓ hℓ) ≫
        P.cyclesPair n m k hnm a b ℓ hℓ =
      P.longPair n m k hnm a b ℓ hℓ ≫ Z.windowToCycles k (a + b) ℓ hℓ := by
  rw [← cancel_mono (Z.windowICycles k (a + b) ℓ hℓ)]
  simp only [Category.assoc, cyclesPair_i, windowToCycles_i]
  rw [← Category.assoc, tensorHom_comp_tensorHom, windowToCycles_i,
    windowToCycles_i, P.longPair_restriction n m k hnm a b ℓ hℓ]

/-- The first-factor boundary product is an output boundary.

A left boundary paired with a long representative factors through the output incoming
boundary. -/
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

/-- The second-factor boundary product is a signed output boundary.

A right boundary paired with a long representative factors through the output boundary with
sign (−1)^n. -/
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

/-- The first-factor boundary vanishes after quotienting the product.

The left boundary paired with any cycle is killed by the output window projection. -/
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

/-- The second-factor boundary vanishes after quotienting the product.

The right boundary paired with any cycle is killed by the output window projection. -/
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

/-- Both tensor boundary sources vanish in the output quotient.

The coproduct of the two boundary-product maps has zero composite with the projected cycle
product. -/
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

/-- The product induced on window boundary quotients.

For 1≤u≤ℓ, descend the cycle product through the two boundary cokernels to the output window
quotient. -/
def windowPair (n m k : ℤ) (hnm : n + m = k)
    (a b ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    X.windowE n a ℓ u hℓ hu ⊗ Y.windowE m b ℓ u hℓ hu ⟶
      Z.windowE k (a + b) ℓ u hℓ hu :=
  CokernelCofork.tensorDesc
    (X.windowCofork n a ℓ u hℓ hu) (X.windowCoforkIsColimit n a ℓ u hℓ hu)
    (Y.windowCofork m b ℓ u hℓ hu) (Y.windowCoforkIsColimit m b ℓ u hℓ hu)
    (P.cyclesPair n m k hnm a b ℓ hℓ ≫ Z.windowπ k (a + b) ℓ u hℓ hu)
    (P.boundaries_quotient_zero n m k hnm a b ℓ u hℓ hu huℓ)

/-- The window product preserves quotient representatives.

The tensor of input projections followed by windowPair equals cyclesPair followed by the
output projection. -/
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

/-- The window product on long-interval representatives.

Represent both input classes by long intervals; their product is longPair followed by the
output representative. -/
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

/-- The window product with a specified additive output cut.

For a+b=s, transport the standard product to the output cut s. -/
def windowPairTo (n m k : ℤ) (hnm : n + m = k) (a b s : ℤ) (hs : a + b = s)
    (ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    X.windowE n a ℓ u hℓ hu ⊗ Y.windowE m b ℓ u hℓ hu ⟶
      Z.windowE k s ℓ u hℓ hu := by
  subst s
  exact P.windowPair n m k hnm a b ℓ u hℓ hu huℓ

/-- The specified-output window product on representatives.

The representative formula uses the interval product with output (s−ℓ,s). -/
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

/-- The first-factor window differential product on representatives.

The representative product of the first differential is the first interval boundary followed
by the shifted interval product. -/
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

/-- The second-factor window differential product on representatives.

The representative product of the second differential is the second interval boundary followed
by the shifted interval product. -/
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

/-- Cycle products commute with lower-width maps.

The tensor of the lower-width cycle maps commutes with the output cycle-width map. -/
@[reassoc]
lemma cyclesPair_map (n m k : ℤ) (hnm : n + m = k) (a b ℓ ℓ' : ℤ)
    (hℓ : 1 ≤ ℓ) (hℓ' : 1 ≤ ℓ') (h : ℓ' ≤ ℓ) :
    (X.windowCyclesMap n a ℓ ℓ' hℓ hℓ' h ⊗ₘ
      Y.windowCyclesMap m b ℓ ℓ' hℓ hℓ' h) ≫ P.cyclesPair n m k hnm a b ℓ' hℓ' =
      P.cyclesPair n m k hnm a b ℓ hℓ ≫ Z.windowCyclesMap k (a + b) ℓ ℓ' hℓ hℓ' h := by
  rw [← cancel_mono (Z.windowICycles k (a + b) ℓ' hℓ')]
  simp only [Category.assoc, cyclesPair_i, windowCyclesMap_i]
  rw [← Category.assoc, tensorHom_comp_tensorHom, windowCyclesMap_i, windowCyclesMap_i]

/-- Window products commute with nested-width maps.

For the stated inequalities on both widths, the tensor of window maps commutes with the output
window map. -/
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

/-- The equal-width window product satisfies Leibniz.

The output window differential equals the first differential product plus (−1)^n times the
second differential product. -/
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

/-- Specified-output window products commute with width maps.

The same nested-width square holds after the additive output-cut identification. -/
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

/-- The product on a skeletal spectral-sequence page.

Use the page-window charts to pair E_r^{p,q}(X) ⊗ E_r^{p′,q′}(Y) into E_r^{p+p′,q+q′}(Z). -/
def pagePair (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).X pq ⊗
      ((Y.skeletalSpectralSequence).page r).X pq' ⟶
        ((Z.skeletalSpectralSequence).page r).X (pq + pq') :=
  ((X.pageWindowIso r hr pq).hom ⊗ₘ (Y.pageWindowIso r hr pq').hom) ≫
    P.windowPairTo (pq.1 + pq.2) (pq'.1 + pq'.2) ((pq + pq').1 + (pq + pq').2)
      (by dsimp; omega) (-pq.1) (-pq'.1) (-(pq + pq').1) (by dsimp; omega)
      r r hr hr le_rfl ≫ (Z.pageWindowIso r hr (pq + pq')).inv

/-- The page product with a specified sum bidegree.

For pq+pq′=t, transport pagePair to the output bidegree t. -/
def pagePairTo (r : ℤ) (hr : 1 ≤ r) (pq pq' t : ℤ × ℤ) (ht : pq + pq' = t) :
    ((X.skeletalSpectralSequence).page r).X pq ⊗
      ((Y.skeletalSpectralSequence).page r).X pq' ⟶
        ((Z.skeletalSpectralSequence).page r).X t := by
  subst t
  exact P.pagePair r hr pq pq'

/-- The page product in specified window coordinates.

Conjugating by the page charts gives windowPairTo at widths (r,r), total degrees and cuts −p. -/
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

/-- The inverse-window form of the page product.

The inverse input charts followed by the page product equal the window product followed by the
inverse output chart. -/
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

/-- The product on cycles of a spectral page.

Pair the (r+1,r)-window descriptions of page cycles and return through the output cycle chart. -/
def pageCyclesPair (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).cycles pq ⊗
      ((Y.skeletalSpectralSequence).page r).cycles pq' ⟶
        ((Z.skeletalSpectralSequence).page r).cycles (pq + pq') :=
  ((X.pageCyclesWindowIso r hr pq).hom ⊗ₘ (Y.pageCyclesWindowIso r hr pq').hom) ≫
    P.windowPairTo (pq.1 + pq.2) (pq'.1 + pq'.2) ((pq + pq').1 + (pq + pq').2)
      (by dsimp; omega) (-pq.1) (-pq'.1) (-(pq + pq').1) (by dsimp; omega)
      (r + 1) r (by omega) hr (by omega) ≫ (Z.pageCyclesWindowIso r hr (pq + pq')).inv

/-- The window construction of a page homology product.

Pair the (r+1,r+1)-window descriptions of the page homologies. -/
def pageHomologyWindowPair (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).homology pq ⊗
      ((Y.skeletalSpectralSequence).page r).homology pq' ⟶
        ((Z.skeletalSpectralSequence).page r).homology (pq + pq') :=
  ((X.pageHomologyWindowIso r hr pq).hom ⊗ₘ (Y.pageHomologyWindowIso r hr pq').hom) ≫
    P.windowPairTo (pq.1 + pq.2) (pq'.1 + pq'.2) ((pq + pq').1 + (pq + pq').2)
      (by dsimp; omega) (-pq.1) (-pq'.1) (-(pq + pq').1) (by dsimp; omega)
      (r + 1) (r + 1) (by omega) (by omega) le_rfl ≫
        (Z.pageHomologyWindowIso r hr (pq + pq')).inv

/-- The page cycle product preserves inclusion.

Its inclusion into the output page equals the tensor of input cycle inclusions followed by
pagePair. -/
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

/-- The window homology product preserves cycle projection.

The tensor of page homology projections followed by the window product equals the page cycle
product followed by output projection. -/
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

/-- Page boundary products vanish after homology projection.

The two incoming boundary sources paired with cycles are killed by the output homology
projection. -/
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

/-- The homology product descended from page cycles.

Descend the page cycle product through the two homology cokernels under tensor coequalizer
preservation. -/
def pageHomologyPair (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page r).homology pq ⊗
      ((Y.skeletalSpectralSequence).page r).homology pq' ⟶
        ((Z.skeletalSpectralSequence).page r).homology (pq + pq') :=
  HomologicalComplex.tensorHomologyDesc
    ((X.skeletalSpectralSequence).page r) ((ComplexShape.up' (r, 1 - r)).prev pq) pq rfl
    ((Y.skeletalSpectralSequence).page r) ((ComplexShape.up' (r, 1 - r)).prev pq') pq' rfl
    (P.pageCyclesPair r hr pq pq' ≫ ((Z.skeletalSpectralSequence).page r).homologyπ (pq + pq'))
    (P.pageCyclesPair_boundaries_zero r hr pq pq')

/-- The descended page homology product preserves projections.

The tensor of input homology projections followed by the descended product equals the cycle
product followed by output projection. -/
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

/-- The descended page homology product equals its window construction.

The cokernel-descended product is pageHomologyWindowPair. -/
lemma pageHomologyPair_eq_windowPair (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    P.pageHomologyPair r hr pq pq' = P.pageHomologyWindowPair r hr pq pq' := by
  apply HomologicalComplex.tensor_homologyπ_hom_ext
    ((X.skeletalSpectralSequence).page r) ((ComplexShape.up' (r, 1 - r)).prev pq) pq rfl
    ((Y.skeletalSpectralSequence).page r) ((ComplexShape.up' (r, 1 - r)).prev pq') pq' rfl
  rw [P.pageHomologyPair_π r hr pq pq', P.pageHomologyWindowPair_π r hr pq pq']

/-- Page products commute with spectral successor isomorphisms.

The page homology product transported to E_{r+1} equals the product of the transported input
homologies. -/
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

/-- The spectral page product satisfies the signed Leibniz rule.

For first bidegree (p,q), d_r(xy)=d_r(x)y+(−1)^{p+q}x d_r(y), with the specified output
bidegree transports. -/
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
