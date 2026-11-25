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

public import MathlibExt.Algebra.Homology.SpectralSequencePairing
public import MathlibExt.Algebra.Homology.SpectralObjectPageMapNaturality

/-!
# Native pairings and morphisms of spectral objects

Original interval components of a spectral-object morphism give maps on the
actual cycle kernels and page quotients. Compatibility on the original
interval products descends through these kernels and cokernels.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory ComposableArrows

universe u v w z

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Hom

variable {ι : Type w} [Category.{z} ι] {X Y : SpectralObject C ι}

/-- The map on the original cycle kernel induced by a spectral-object morphism. -/
def cyclesComponent (φ : X ⟶ Y) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    X.cycles f g n ⟶ Y.cycles f g n :=
  Y.liftCycles f g n (n + 1) rfl (X.iCycles f g n ≫ (φ.hom n).app (mk₁ g)) (by
    rw [Category.assoc, ← φ.comm n (n + 1) rfl f g,
      ← Category.assoc, X.iCycles_δ f g n (n + 1) rfl, zero_comp])

@[reassoc (attr := simp)]
lemma cyclesComponent_i (φ : X ⟶ Y) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    cyclesComponent φ f g n ≫ Y.iCycles f g n =
      X.iCycles f g n ≫ (φ.hom n).app (mk₁ g) :=
  Y.liftCycles_i ..

/-- The original long-interval representatives commute with the induced cycle map. -/
@[reassoc]
lemma toCycles_cyclesComponent (φ : X ⟶ Y) {i j k : ι}
    (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k) (hfg : f ≫ g = fg) (n : ℤ) :
    X.toCycles f g fg hfg n ≫ cyclesComponent φ f g n =
      (φ.hom n).app (mk₁ fg) ≫ Y.toCycles f g fg hfg n := by
  rw [← cancel_mono (Y.iCycles f g n), Category.assoc, cyclesComponent_i,
    X.toCycles_i_assoc, Category.assoc, Y.toCycles_i]
  exact (φ.hom n).naturality (twoδ₁Toδ₀ f g fg hfg)

set_option backward.isDefEq.respectTransparency false in
private lemma cyclesIso_inv_cyclesComponent (φ : X ⟶ Y) {i j k l : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
        ShortComplex.cyclesMap (shortComplexMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) =
      cyclesComponent φ f₁ f₂ n₁ ≫ (Y.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv := by
  rw [← cancel_mono (Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The genuine cycle quotient projection commutes with the original induced `EMap`. -/
@[reassoc]
lemma πE_EMap_component (φ : X ⟶ Y) {i j k l : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ EMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      cyclesComponent φ f₁ f₂ n₁ ≫ Y.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  simp only [SpectralObject.πE, EMap, Category.assoc, ShortComplex.homologyπ_naturality]
  rw [← Category.assoc, cyclesIso_inv_cyclesComponent φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂,
    Category.assoc]

end Hom

namespace Hom

variable {X Y : SpectralObject C EInt}

/-- The original component on a finite integer interval. -/
abbrev intervalComponent (φ : X ⟶ Y) (n a b : ℤ) (hab : a ≤ b) :
    X.intervalH n a b hab ⟶ Y.intervalH n a b hab :=
  (φ.hom n).app (mk₁ (homOfLE (show (a : EInt) ≤ (b : EInt) by simpa using hab)))

/-- The original morphism acts on the actual cycles in a finite window. -/
abbrev windowCyclesHom (φ : X ⟶ Y) (n a ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.windowCycles n a ℓ hℓ ⟶ Y.windowCycles n a ℓ hℓ :=
  cyclesComponent φ
    (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by simp; omega))
    (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp)) n

/-- The map on the original finite quotient window is its original `EMap`. -/
abbrev windowHom (φ : X ⟶ Y) (n a ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    X.windowE n a ℓ u hℓ hu ⟶ Y.windowE n a ℓ u hℓ hu :=
  EMap φ
    (homOfLE (show ((a - ℓ : ℤ) : EInt) ≤ ((a - 1 : ℤ) : EInt) by simp; omega))
    (homOfLE (show ((a - 1 : ℤ) : EInt) ≤ (a : EInt) by simp))
    (homOfLE (show (a : EInt) ≤ ((a + u - 1 : ℤ) : EInt) by simp; omega))
    (n - 1) n (n + 1)

/- The original cyclesComponent equations already simplify these window aliases.
Keep both named equations available for explicit rewriting and reassociation. -/
@[reassoc]
lemma windowCyclesHom_i (φ : X ⟶ Y) (n a ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    windowCyclesHom φ n a ℓ hℓ ≫ Y.windowICycles n a ℓ hℓ =
      X.windowICycles n a ℓ hℓ ≫ intervalComponent φ n (a - 1) a (by omega) :=
  cyclesComponent_i φ _ _ n

@[reassoc]
lemma windowToCycles_windowCyclesHom (φ : X ⟶ Y) (n a ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.windowToCycles n a ℓ hℓ ≫ windowCyclesHom φ n a ℓ hℓ =
      intervalComponent φ n (a - ℓ) a (by omega) ≫ Y.windowToCycles n a ℓ hℓ :=
  toCycles_cyclesComponent φ _ _ _ (by cat_disch) n

@[reassoc]
lemma windowπ_windowHom (φ : X ⟶ Y) (n a ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    X.windowπ n a ℓ u hℓ hu ≫ windowHom φ n a ℓ u hℓ hu =
      windowCyclesHom φ n a ℓ hℓ ≫ Y.windowπ n a ℓ u hℓ hu :=
  πE_EMap_component φ _ _ _ (n - 1) n (n + 1) (by omega) rfl

unseal SpectralObject.spectralSequence in
set_option backward.isDefEq.respectTransparency false in
/-- The genuine native page map is the original window map under the canonical page iso. -/
@[reassoc]
lemma pageMap_pageWindowIso (φ : X ⟶ Y) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
    (φ.spectralSequencePageMap skeletalPageCore r hr).f pq ≫ (Y.pageWindowIso r hr pq).hom =
      (X.pageWindowIso r hr pq).hom ≫ windowHom φ (pq.1 + pq.2) (-pq.1) r r hr hr := by
  simpa only [spectralSequencePageMap, skeletalSpectralSequence, spectralSequence,
    pageWindowIso, spectralSequencePageXIso, windowHom, pageMap] using
    pageMapComponent_pageXIso_hom φ skeletalPageCore r hr pq
      ((-pq.1 - r : ℤ) : EInt) ((-pq.1 - 1 : ℤ) : EInt)
      ((-pq.1 : ℤ) : EInt) ((-pq.1 + r - 1 : ℤ) : EInt)
      rfl rfl rfl rfl (pq.1 + pq.2 - 1) (pq.1 + pq.2) (pq.1 + pq.2 + 1) rfl (by omega) rfl

/-- The inverse page iso commutes with the original native page map. -/
@[reassoc]
lemma windowHom_pageWindowIso_inv (φ : X ⟶ Y) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
    windowHom φ (pq.1 + pq.2) (-pq.1) r r hr hr ≫ (Y.pageWindowIso r hr pq).inv =
      (X.pageWindowIso r hr pq).inv ≫ (φ.spectralSequencePageMap skeletalPageCore r hr).f pq := by
  apply (cancel_epi (X.pageWindowIso r hr pq).hom).mp
  rw [← Category.assoc, ← pageMap_pageWindowIso φ r hr pq]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end Hom

namespace IntervalPairing

variable [MonoidalCategory C] [MonoidalPreadditive C]
  {X Y Z X' Y' Z' : SpectralObject C EInt}
  (P : IntervalPairing X Y Z) (P' : IntervalPairing X' Y' Z')
  (α : X ⟶ X') (β : Y ⟶ Y') (γ : Z ⟶ Z')

/-- Compatibility concerns only the original interval products and original spectral-object components. -/
def IsCompatible : Prop :=
  ∀ (n m k A a B b s t : ℤ) (hnm : n + m = k)
    (hAa : A ≤ a) (hBb : B ≤ b) (hst : s ≤ t)
    (hleft : A + b ≤ s) (hright : a + B ≤ s) (hupper : a + b ≤ t),
    (Hom.intervalComponent α n A a hAa ⊗ₘ Hom.intervalComponent β m B b hBb) ≫
        P'.pair n m k A a B b s t hnm hAa hBb hst hleft hright hupper =
      P.pair n m k A a B b s t hnm hAa hBb hst hleft hright hupper ≫
        Hom.intervalComponent γ k s t hst

variable {P P' α β γ}

omit [MonoidalPreadditive C] in
/-- Original compatible interval products preserve the actual short-interval product. -/
lemma IsCompatible.shortPair (hP : P.IsCompatible P' α β γ)
    (n m k : ℤ) (hnm : n + m = k) (a b : ℤ) :
    (Hom.intervalComponent α n (a - 1) a (by omega) ⊗ₘ
      Hom.intervalComponent β m (b - 1) b (by omega)) ≫ P'.shortPair n m k hnm a b =
      P.shortPair n m k hnm a b ≫ Hom.intervalComponent γ k (a + b - 1) (a + b) (by omega) :=
  hP n m k (a - 1) a (b - 1) b (a + b - 1) (a + b) hnm
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

variable [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)]

/-- Kernel inclusion descends original interval compatibility to the actual native cycle product. -/
lemma IsCompatible.cyclesPair (hP : P.IsCompatible P' α β γ)
    (n m k : ℤ) (hnm : n + m = k) (a b ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    (Hom.windowCyclesHom α n a ℓ hℓ ⊗ₘ Hom.windowCyclesHom β m b ℓ hℓ) ≫
        P'.cyclesPair n m k hnm a b ℓ hℓ =
      P.cyclesPair n m k hnm a b ℓ hℓ ≫ Hom.windowCyclesHom γ k (a + b) ℓ hℓ := by
  rw [← cancel_mono (Z'.windowICycles k (a + b) ℓ hℓ)]
  simp only [Category.assoc, IntervalPairing.cyclesPair_i, Hom.windowCyclesHom_i]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Hom.windowCyclesHom_i, Hom.windowCyclesHom_i,
    ← tensorHom_comp_tensorHom_assoc, hP.shortPair n m k hnm a b,
    IntervalPairing.cyclesPair_i_assoc]

private lemma tensor_epimorphism {A B D F : C} (f : A ⟶ B) (g : D ⟶ F)
    [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  let c₁ : CokernelCofork (kernel.ι f) := CokernelCofork.ofπ f (kernel.condition f)
  let c₂ : CokernelCofork (kernel.ι g) := CokernelCofork.ofπ g (kernel.condition g)
  exact CokernelCofork.epi_tensor_π c₁ (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _))
    c₂ (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _))

/-- The original cycle quotient maps descend interval compatibility to the actual native window product. -/
lemma IsCompatible.windowPair (hP : P.IsCompatible P' α β γ)
    (n m k : ℤ) (hnm : n + m = k) (a b ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    (Hom.windowHom α n a ℓ u hℓ hu ⊗ₘ Hom.windowHom β m b ℓ u hℓ hu) ≫
        P'.windowPair n m k hnm a b ℓ u hℓ hu huℓ =
      P.windowPair n m k hnm a b ℓ u hℓ hu huℓ ≫ Hom.windowHom γ k (a + b) ℓ u hℓ hu := by
  letI : Epi (X.windowπ n a ℓ u hℓ hu ⊗ₘ Y.windowπ m b ℓ u hℓ hu) := tensor_epimorphism _ _
  rw [← cancel_epi (X.windowπ n a ℓ u hℓ hu ⊗ₘ Y.windowπ m b ℓ u hℓ hu)]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Hom.windowπ_windowHom, Hom.windowπ_windowHom,
    ← tensorHom_comp_tensorHom_assoc, IntervalPairing.quotient_windowPair]
  rw [IntervalPairing.quotient_windowPair_assoc, Hom.windowπ_windowHom]
  rw [← Category.assoc, hP.cyclesPair n m k hnm a b ℓ hℓ, Category.assoc]

/-- The same descended compatibility with an explicitly equal output cut. -/
lemma IsCompatible.windowPairTo (hP : P.IsCompatible P' α β γ)
    (n m k : ℤ) (hnm : n + m = k) (a b s : ℤ) (hs : a + b = s) (ℓ u : ℤ)
    (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    (Hom.windowHom α n a ℓ u hℓ hu ⊗ₘ Hom.windowHom β m b ℓ u hℓ hu) ≫
        P'.windowPairTo n m k hnm a b s hs ℓ u hℓ hu huℓ =
      P.windowPairTo n m k hnm a b s hs ℓ u hℓ hu huℓ ≫ Hom.windowHom γ k s ℓ u hℓ hu := by
  subst s
  exact hP.windowPair n m k hnm a b ℓ u hℓ hu huℓ

omit [Abelian C] [MonoidalPreadditive C]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)] in
private lemma page_pairing_transport {A B A' B' L R L' R' U U' P P' : C}
    (a : A ⟶ A') (b : B ⟶ B') (l : A ⟶ L) (r : B ⟶ R) (l' : A' ⟶ L') (r' : B' ⟶ R')
    (cl : L ⟶ L') (cr : R ⟶ R') (cu : U ⟶ U') (cp : P ⟶ P')
    (cup : L ⊗ R ⟶ U) (cup' : L' ⊗ R' ⟶ U') (out : U ⟶ P) (out' : U' ⟶ P')
    (hl : a ≫ l' = l ≫ cl) (hr : b ≫ r' = r ≫ cr)
    (hc : (cl ⊗ₘ cr) ≫ cup' = cup ≫ cu) (ho : cu ≫ out' = out ≫ cp) :
    (a ⊗ₘ b) ≫ (l' ⊗ₘ r') ≫ cup' ≫ out' = ((l ⊗ₘ r) ≫ cup ≫ out) ≫ cp := by
  rw [tensorHom_comp_tensorHom_assoc, hl, hr, ← tensorHom_comp_tensorHom_assoc]
  rw [← Category.assoc (cl ⊗ₘ cr) cup' out', hc]
  simp only [Category.assoc]
  rw [ho]

/-- Original interval compatibility preserves the actual native product on every integer page. -/
lemma IsCompatible.pagePair (hP : P.IsCompatible P' α β γ)
    (r : ℤ) (hr : 1 ≤ r) (pq pq' : ℤ × ℤ) :
    ((α.spectralSequencePageMap skeletalPageCore r hr).f pq ⊗ₘ
      (β.spectralSequencePageMap skeletalPageCore r hr).f pq') ≫ P'.pagePair r hr pq pq' =
      P.pagePair r hr pq pq' ≫ (γ.spectralSequencePageMap skeletalPageCore r hr).f (pq + pq') := by
  have hl := Hom.pageMap_pageWindowIso α r hr pq
  have hb := Hom.pageMap_pageWindowIso β r hr pq'
  have hc := hP.windowPairTo (pq.1 + pq.2) (pq'.1 + pq'.2) ((pq + pq').1 + (pq + pq').2)
    (by dsimp; omega) (-pq.1) (-pq'.1) (-(pq + pq').1) (by dsimp; omega) r r hr hr le_rfl
  have ho := Hom.windowHom_pageWindowIso_inv γ r hr (pq + pq')
  exact page_pairing_transport _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl hb hc ho

/-- Original interval compatibility preserves the native cup at any equal output bidegree. -/
lemma IsCompatible.pagePairTo (hP : P.IsCompatible P' α β γ)
    (r : ℤ) (hr : 1 ≤ r) (pq pq' t : ℤ × ℤ) (ht : pq + pq' = t) :
    ((α.spectralSequencePageMap skeletalPageCore r hr).f pq ⊗ₘ
      (β.spectralSequencePageMap skeletalPageCore r hr).f pq') ≫ P'.pagePairTo r hr pq pq' t ht =
      P.pagePairTo r hr pq pq' t ht ≫ (γ.spectralSequencePageMap skeletalPageCore r hr).f t := by
  subst t
  exact hP.pagePair r hr pq pq'

end IntervalPairing

end CategoryTheory.Abelian.SpectralObject
