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

public import MathlibExt.Algebra.Homology.SpectralSequencePairingNaturality
public import MathlibExt.Algebra.Homology.GenericSpectralSequenceMapCompatibility
public import MathlibExt.CategoryTheory.Monoidal.PairingDescentCoherence

/-!
# Mixed associativity of native spectral-sequence pairings

Four original interval pairings and an original spectral-object map determine
the two ways to multiply three inputs. Their long-interval equality descends
through the actual cycle and quotient representatives to the native windows
and pages. All products and comparison maps are the existing native maps.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits MonoidalCategory

universe u v

namespace CategoryTheory.Abelian.SpectralObject.IntervalPairing

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)]
  {X Y Z U V L W : SpectralObject C EInt}

/-- The original long-interval product with an explicitly equal output cut. -/
def longPairTo (P : IntervalPairing X Y U) (n m k : ℤ) (hnm : n + m = k)
    (a b s : ℤ) (hs : a + b = s) (ℓ : ℤ) (hℓ : 1 ≤ ℓ) :
    X.intervalH n (a - ℓ) a (by omega) ⊗ Y.intervalH m (b - ℓ) b (by omega) ⟶
      U.intervalH k (s - ℓ) s (by omega) :=
  P.pair n m k (a - ℓ) a (b - ℓ) b (s - ℓ) s hnm
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The actual representatives retain the explicit-cut original long product. -/
@[reassoc]
lemma longPairTo_representatives (P : IntervalPairing X Y U)
    (n m k : ℤ) (hnm : n + m = k) (a b s : ℤ) (hs : a + b = s)
    (ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ) :
    P.longPairTo n m k hnm a b s hs ℓ hℓ ≫
        U.windowToCycles k s ℓ hℓ ≫ U.windowπ k s ℓ u hℓ hu =
      ((X.windowToCycles n a ℓ hℓ ≫ X.windowπ n a ℓ u hℓ hu) ⊗ₘ
        (Y.windowToCycles m b ℓ hℓ ≫ Y.windowπ m b ℓ u hℓ hu)) ≫
          P.windowPairTo n m k hnm a b s hs ℓ u hℓ hu huℓ :=
  (P.representatives_windowPairTo n m k hnm a b s hs ℓ u hℓ hu huℓ).symm

omit [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)] in
/-- The original output map commutes with the full cycle-and-quotient representative. -/
@[reassoc]
lemma longRepresentative_windowHom (γ : L ⟶ W)
    (n a ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) :
    Hom.intervalComponent γ n (a - ℓ) a (by omega) ≫
        W.windowToCycles n a ℓ hℓ ≫ W.windowπ n a ℓ u hℓ hu =
      (L.windowToCycles n a ℓ hℓ ≫ L.windowπ n a ℓ u hℓ hu) ≫
        Hom.windowHom γ n a ℓ u hℓ hu := by
  rw [Category.assoc, Hom.windowπ_windowHom,
    Hom.windowToCycles_windowCyclesHom_assoc]

/-- An equality of the original three long-interval products descends to the genuine quotient windows. -/
theorem windowPairTo_associativity
    (P : IntervalPairing X Y U) (Q : IntervalPairing U Z L)
    (R : IntervalPairing Y Z V) (T : IntervalPairing X V W) (γ : L ⟶ W)
    (n m k a b c ℓ u : ℤ) (hℓ : 1 ≤ ℓ) (hu : 1 ≤ u) (huℓ : u ≤ ℓ)
    (hassoc :
      (P.longPairTo n m (n + m) rfl a b (a + b) rfl ℓ hℓ ⊗ₘ
          𝟙 (Z.intervalH k (c - ℓ) c (by omega))) ≫
        Q.longPairTo (n + m) k (n + (m + k)) (add_assoc n m k)
          (a + b) c (a + (b + c)) (add_assoc a b c) ℓ hℓ ≫
        Hom.intervalComponent γ (n + (m + k)) (a + (b + c) - ℓ) (a + (b + c)) (by omega) =
      (α_ (X.intervalH n (a - ℓ) a (by omega)) (Y.intervalH m (b - ℓ) b (by omega))
        (Z.intervalH k (c - ℓ) c (by omega))).hom ≫
        (𝟙 _ ⊗ₘ R.longPairTo m k (m + k) rfl b c (b + c) rfl ℓ hℓ) ≫
        T.longPairTo n (m + k) (n + (m + k)) rfl a (b + c) (a + (b + c)) rfl ℓ hℓ) :
    (P.windowPairTo n m (n + m) rfl a b (a + b) rfl ℓ u hℓ hu huℓ ⊗ₘ
        𝟙 (Z.windowE k c ℓ u hℓ hu)) ≫
      Q.windowPairTo (n + m) k (n + (m + k)) (add_assoc n m k)
        (a + b) c (a + (b + c)) (add_assoc a b c) ℓ u hℓ hu huℓ ≫
      Hom.windowHom γ (n + (m + k)) (a + (b + c)) ℓ u hℓ hu =
    (α_ (X.windowE n a ℓ u hℓ hu) (Y.windowE m b ℓ u hℓ hu)
      (Z.windowE k c ℓ u hℓ hu)).hom ≫
      (𝟙 _ ⊗ₘ R.windowPairTo m k (m + k) rfl b c (b + c) rfl ℓ u hℓ hu huℓ) ≫
      T.windowPairTo n (m + k) (n + (m + k)) rfl a (b + c) (a + (b + c)) rfl ℓ u hℓ hu huℓ := by
  let eX := X.windowToCycles n a ℓ hℓ ≫ X.windowπ n a ℓ u hℓ hu
  let eY := Y.windowToCycles m b ℓ hℓ ≫ Y.windowπ m b ℓ u hℓ hu
  let eZ := Z.windowToCycles k c ℓ hℓ ≫ Z.windowπ k c ℓ u hℓ hu
  let eU := U.windowToCycles (n + m) (a + b) ℓ hℓ ≫ U.windowπ (n + m) (a + b) ℓ u hℓ hu
  let eV := V.windowToCycles (m + k) (b + c) ℓ hℓ ≫ V.windowπ (m + k) (b + c) ℓ u hℓ hu
  let eL := L.windowToCycles (n + (m + k)) (a + (b + c)) ℓ hℓ ≫
    L.windowπ (n + (m + k)) (a + (b + c)) ℓ u hℓ hu
  let eW := W.windowToCycles (n + (m + k)) (a + (b + c)) ℓ hℓ ≫
    W.windowπ (n + (m + k)) (a + (b + c)) ℓ u hℓ hu
  let : Epi (eX ⊗ₘ eY) := epi_tensorHom_of_preservesCokernels _ _
  let : Epi ((eX ⊗ₘ eY) ⊗ₘ eZ) := epi_tensorHom_of_preservesCokernels _ _
  exact pairing_associativity_of_epi_projection eX eY eZ eU eV eL eW
    (P.longPairTo n m (n + m) rfl a b (a + b) rfl ℓ hℓ)
    (Q.longPairTo (n + m) k (n + (m + k)) (add_assoc n m k)
      (a + b) c (a + (b + c)) (add_assoc a b c) ℓ hℓ)
    (R.longPairTo m k (m + k) rfl b c (b + c) rfl ℓ hℓ)
    (T.longPairTo n (m + k) (n + (m + k)) rfl a (b + c) (a + (b + c)) rfl ℓ hℓ)
    (P.windowPairTo n m (n + m) rfl a b (a + b) rfl ℓ u hℓ hu huℓ)
    (Q.windowPairTo (n + m) k (n + (m + k)) (add_assoc n m k)
      (a + b) c (a + (b + c)) (add_assoc a b c) ℓ u hℓ hu huℓ)
    (R.windowPairTo m k (m + k) rfl b c (b + c) rfl ℓ u hℓ hu huℓ)
    (T.windowPairTo n (m + k) (n + (m + k)) rfl a (b + c) (a + (b + c)) rfl ℓ u hℓ hu huℓ)
    (Hom.intervalComponent γ (n + (m + k)) (a + (b + c) - ℓ) (a + (b + c)) (by omega))
    (Hom.windowHom γ (n + (m + k)) (a + (b + c)) ℓ u hℓ hu)
    (P.longPairTo_representatives n m (n + m) rfl a b (a + b) rfl ℓ u hℓ hu huℓ)
    (Q.longPairTo_representatives (n + m) k (n + (m + k)) (add_assoc n m k)
      (a + b) c (a + (b + c)) (add_assoc a b c) ℓ u hℓ hu huℓ)
    (R.longPairTo_representatives m k (m + k) rfl b c (b + c) rfl ℓ u hℓ hu huℓ)
    (T.longPairTo_representatives n (m + k) (n + (m + k)) rfl a (b + c) (a + (b + c)) rfl ℓ u hℓ hu huℓ)
    (longRepresentative_windowHom γ (n + (m + k)) (a + (b + c)) ℓ u hℓ hu) hassoc

/-- Mixed associativity concerns only the original products on three equal-length long intervals. -/
def longAssociativity
    (P : IntervalPairing X Y U) (Q : IntervalPairing U Z L)
    (R : IntervalPairing Y Z V) (T : IntervalPairing X V W) (γ : L ⟶ W)
    (ℓ : ℤ) (hℓ : 1 ≤ ℓ) : Prop :=
  ∀ n m k a b c : ℤ,
    (P.longPairTo n m (n + m) rfl a b (a + b) rfl ℓ hℓ ⊗ₘ
        𝟙 (Z.intervalH k (c - ℓ) c (by omega))) ≫
      Q.longPairTo (n + m) k (n + (m + k)) (add_assoc n m k)
        (a + b) c (a + (b + c)) (add_assoc a b c) ℓ hℓ ≫
      Hom.intervalComponent γ (n + (m + k)) (a + (b + c) - ℓ) (a + (b + c)) (by omega) =
    (α_ (X.intervalH n (a - ℓ) a (by omega)) (Y.intervalH m (b - ℓ) b (by omega))
      (Z.intervalH k (c - ℓ) c (by omega))).hom ≫
      (𝟙 _ ⊗ₘ R.longPairTo m k (m + k) rfl b c (b + c) rfl ℓ hℓ) ≫
      T.longPairTo n (m + k) (n + (m + k)) rfl a (b + c) (a + (b + c)) rfl ℓ hℓ

/-- The original page product followed by the original page-window comparison is the window product. -/
@[reassoc]
lemma pagePairTo_window_hom (P : IntervalPairing X Y U)
    (r : ℤ) (hr : 1 ≤ r) (pq pq' t : ℤ × ℤ) (ht : pq + pq' = t)
    (n m k a b s : ℤ) (hn : n = pq.1 + pq.2) (hm : m = pq'.1 + pq'.2)
    (hk : k = t.1 + t.2) (ha : a = -pq.1) (hb : b = -pq'.1) (hs : s = -t.1)
    (hnm : n + m = k) (hab : a + b = s) :
    P.pagePairTo r hr pq pq' t ht ≫ (U.pageWindowIsoAt r hr t k s hk hs).hom =
      ((X.pageWindowIsoAt r hr pq n a hn ha).hom ⊗ₘ
        (Y.pageWindowIsoAt r hr pq' m b hm hb).hom) ≫
          P.windowPairTo n m k hnm a b s hab r r hr hr le_rfl := by
  let eX := X.pageWindowIsoAt r hr pq n a hn ha
  let eY := Y.pageWindowIsoAt r hr pq' m b hm hb
  let eU := U.pageWindowIsoAt r hr t k s hk hs
  have h := P.pagePairTo_window r hr pq pq' t ht n m k a b s hn hm hk ha hb hs hnm hab
  change P.pagePairTo r hr pq pq' t ht ≫ eU.hom =
    (eX.hom ⊗ₘ eY.hom) ≫ P.windowPairTo n m k hnm a b s hab r r hr hr le_rfl
  apply (cancel_epi (eX.inv ⊗ₘ eY.inv)).mp
  rw [h, tensorHom_comp_tensorHom_assoc]
  simp only [Iso.inv_hom_id, tensorHom_id, id_whiskerRight, Category.id_comp]

omit [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)] in
/-- The original output page map retains independently chosen, equal degree and cut notation. -/
@[reassoc]
lemma pageMap_pageWindowIsoAt (γ : L ⟶ W) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ)
    (n a : ℤ) (hn : n = pq.1 + pq.2) (ha : a = -pq.1) :
    (γ.spectralSequencePageMap skeletalPageCore r hr).f pq ≫
        (W.pageWindowIsoAt r hr pq n a hn ha).hom =
      (L.pageWindowIsoAt r hr pq n a hn ha).hom ≫ Hom.windowHom γ n a r r hr hr := by
  subst n a
  exact Hom.pageMap_pageWindowIso γ r hr pq

/-- The long-interval associativity equation gives the actual native mixed page equation. -/
theorem pagePairTo_associativity
    (P : IntervalPairing X Y U) (Q : IntervalPairing U Z L)
    (R : IntervalPairing Y Z V) (T : IntervalPairing X V W) (γ : L ⟶ W)
    (r : ℤ) (hr : 1 ≤ r) (hassoc : longAssociativity P Q R T γ r hr)
    (pq pq' pq'' : ℤ × ℤ) :
    (P.pagePair r hr pq pq' ⊗ₘ 𝟙 (((Z.skeletalSpectralSequence).page r).X pq'')) ≫
      Q.pagePairTo r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq'') ≫
      (γ.spectralSequencePageMap skeletalPageCore r hr).f (pq + (pq' + pq'')) =
    (α_ (((X.skeletalSpectralSequence).page r).X pq) (((Y.skeletalSpectralSequence).page r).X pq')
      (((Z.skeletalSpectralSequence).page r).X pq'')).hom ≫
      (𝟙 _ ⊗ₘ R.pagePair r hr pq' pq'') ≫ T.pagePair r hr pq (pq' + pq'') := by
  let n := pq.1 + pq.2
  let m := pq'.1 + pq'.2
  let k := pq''.1 + pq''.2
  let a := -pq.1
  let b := -pq'.1
  let c := -pq''.1
  let eX := X.pageWindowIsoAt r hr pq n a rfl rfl
  let eY := Y.pageWindowIsoAt r hr pq' m b rfl rfl
  let eZ := Z.pageWindowIsoAt r hr pq'' k c rfl rfl
  let eU := U.pageWindowIsoAt r hr (pq + pq') (n + m) (a + b)
    (by dsimp; omega) (by dsimp; omega)
  let eV := V.pageWindowIsoAt r hr (pq' + pq'') (m + k) (b + c)
    (by dsimp; omega) (by dsimp; omega)
  let eL := L.pageWindowIsoAt r hr (pq + (pq' + pq'')) (n + (m + k)) (a + (b + c))
    (by dsimp; omega) (by dsimp; omega)
  let eW := W.pageWindowIsoAt r hr (pq + (pq' + pq'')) (n + (m + k)) (a + (b + c))
    (by dsimp; omega) (by dsimp; omega)
  exact pairing_associativity_of_mono_projection eX.hom eY.hom eZ.hom eU.hom eV.hom eL.hom eW.hom
    (P.pagePair r hr pq pq')
    (Q.pagePairTo r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq''))
    (R.pagePair r hr pq' pq'') (T.pagePair r hr pq (pq' + pq''))
    (P.windowPairTo n m (n + m) rfl a b (a + b) rfl r r hr hr le_rfl)
    (Q.windowPairTo (n + m) k (n + (m + k)) (add_assoc n m k)
      (a + b) c (a + (b + c)) (add_assoc a b c) r r hr hr le_rfl)
    (R.windowPairTo m k (m + k) rfl b c (b + c) rfl r r hr hr le_rfl)
    (T.windowPairTo n (m + k) (n + (m + k)) rfl a (b + c) (a + (b + c)) rfl r r hr hr le_rfl)
    ((γ.spectralSequencePageMap skeletalPageCore r hr).f (pq + (pq' + pq'')))
    (Hom.windowHom γ (n + (m + k)) (a + (b + c)) r r hr hr)
    (P.pagePairTo_window_hom r hr pq pq' (pq + pq') rfl n m (n + m) a b (a + b) rfl rfl
      (by dsimp; omega) rfl rfl (by dsimp; omega) rfl rfl)
    (Q.pagePairTo_window_hom r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq'')
      (n + m) k (n + (m + k)) (a + b) c (a + (b + c)) (by dsimp; omega) rfl
      (by dsimp; omega) (by dsimp; omega) rfl (by dsimp; omega) (add_assoc n m k) (add_assoc a b c))
    (R.pagePairTo_window_hom r hr pq' pq'' (pq' + pq'') rfl m k (m + k) b c (b + c) rfl rfl
      (by dsimp; omega) rfl rfl (by dsimp; omega) rfl rfl)
    (T.pagePairTo_window_hom r hr pq (pq' + pq'') (pq + (pq' + pq'')) rfl
      n (m + k) (n + (m + k)) a (b + c) (a + (b + c)) rfl (by dsimp; omega)
      (by dsimp; omega) rfl (by dsimp; omega) (by dsimp; omega) rfl rfl)
    (pageMap_pageWindowIsoAt γ r hr (pq + (pq' + pq'')) (n + (m + k)) (a + (b + c))
      (by dsimp; omega) (by dsimp; omega))
    (windowPairTo_associativity P Q R T γ n m k a b c r r hr hr le_rfl (hassoc n m k a b c))

/-- Mixed associativity is the equality of the original four native page products and original output map. -/
def mixedPageAssociativity
    (P : IntervalPairing X Y U) (Q : IntervalPairing U Z L)
    (R : IntervalPairing Y Z V) (T : IntervalPairing X V W) (γ : L ⟶ W)
    (r : ℤ) (hr : 1 ≤ r) : Prop :=
  ∀ pq pq' pq'' : ℤ × ℤ,
    (P.pagePair r hr pq pq' ⊗ₘ 𝟙 (((Z.skeletalSpectralSequence).page r).X pq'')) ≫
      Q.pagePairTo r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq'') ≫
      (γ.spectralSequencePageMap skeletalPageCore r hr).f (pq + (pq' + pq'')) =
    (α_ (((X.skeletalSpectralSequence).page r).X pq) (((Y.skeletalSpectralSequence).page r).X pq')
      (((Z.skeletalSpectralSequence).page r).X pq'')).hom ≫
      (𝟙 _ ⊗ₘ R.pagePair r hr pq' pq'') ≫ T.pagePair r hr pq (pq' + pq'')

/-- The earned long-interval law supplies mixed associativity on every original native page. -/
theorem mixedPageAssociativity_of_long
    (P : IntervalPairing X Y U) (Q : IntervalPairing U Z L)
    (R : IntervalPairing Y Z V) (T : IntervalPairing X V W) (γ : L ⟶ W)
    (r : ℤ) (hr : 1 ≤ r) (hassoc : longAssociativity P Q R T γ r hr) :
    mixedPageAssociativity P Q R T γ r hr :=
  pagePairTo_associativity P Q R T γ r hr hassoc

/-- The original mixed cycle product with an explicitly equal output bidegree. -/
def mixedPageCyclesPairTo (P : IntervalPairing X Y U)
    (r : ℤ) (hr : 1 ≤ r) (pq pq' t : ℤ × ℤ) (ht : pq + pq' = t) :
    ((X.skeletalSpectralSequence).page r).cycles pq ⊗ ((Y.skeletalSpectralSequence).page r).cycles pq' ⟶
      ((U.skeletalSpectralSequence).page r).cycles t := by
  subst t
  exact P.pageCyclesPair r hr pq pq'

/-- The original mixed homology product with an explicitly equal output bidegree. -/
def mixedPageHomologyPairTo (P : IntervalPairing X Y U)
    (r : ℤ) (hr : 1 ≤ r) (pq pq' t : ℤ × ℤ) (ht : pq + pq' = t) :
    ((X.skeletalSpectralSequence).page r).homology pq ⊗ ((Y.skeletalSpectralSequence).page r).homology pq' ⟶
      ((U.skeletalSpectralSequence).page r).homology t := by
  subst t
  exact P.pageHomologyPair r hr pq pq'

/-- The mixed cycle product is computed by the original native kernel inclusions. -/
@[reassoc]
lemma mixedPageCyclesPairTo_i (P : IntervalPairing X Y U)
    (r : ℤ) (hr : 1 ≤ r) (pq pq' t : ℤ × ℤ) (ht : pq + pq' = t) :
    P.mixedPageCyclesPairTo r hr pq pq' t ht ≫ ((U.skeletalSpectralSequence).page r).iCycles t =
      (((X.skeletalSpectralSequence).page r).iCycles pq ⊗ₘ
        ((Y.skeletalSpectralSequence).page r).iCycles pq') ≫ P.pagePairTo r hr pq pq' t ht := by
  subst t
  exact P.pageCyclesPair_i r hr pq pq'

/-- The mixed homology product is computed by the original native quotient projections. -/
@[reassoc]
lemma mixedPageHomologyPairTo_π (P : IntervalPairing X Y U)
    (r : ℤ) (hr : 1 ≤ r) (pq pq' t : ℤ × ℤ) (ht : pq + pq' = t) :
    (((X.skeletalSpectralSequence).page r).homologyπ pq ⊗ₘ
      ((Y.skeletalSpectralSequence).page r).homologyπ pq') ≫ P.mixedPageHomologyPairTo r hr pq pq' t ht =
      P.mixedPageCyclesPairTo r hr pq pq' t ht ≫ ((U.skeletalSpectralSequence).page r).homologyπ t := by
  subst t
  exact P.pageHomologyPair_π r hr pq pq'

/-- The actual native successor comparisons carry the mixed homology product to the next page product. -/
@[reassoc]
lemma mixedPageHomologyPairTo_successor (P : IntervalPairing X Y U)
    (r : ℤ) (hr : 1 ≤ r) (pq pq' t : ℤ × ℤ) (ht : pq + pq' = t) :
    P.mixedPageHomologyPairTo r hr pq pq' t ht ≫
        (U.skeletalSpectralSequence.iso r (r + 1) t rfl hr).hom =
      ((X.skeletalSpectralSequence.iso r (r + 1) pq rfl hr).hom ⊗ₘ
        (Y.skeletalSpectralSequence.iso r (r + 1) pq' rfl hr).hom) ≫
        P.pagePairTo (r + 1) (by omega) pq pq' t ht := by
  subst t
  exact P.pagePair_successor r hr pq pq'

/-- The inverse successor comparisons retain the original mixed homology product. -/
@[reassoc]
lemma mixedPagePairTo_successor_inv (P : IntervalPairing X Y U)
    (r : ℤ) (hr : 1 ≤ r) (pq pq' t : ℤ × ℤ) (ht : pq + pq' = t) :
    P.pagePairTo (r + 1) (by omega) pq pq' t ht ≫
        (U.skeletalSpectralSequence.iso r (r + 1) t rfl hr).inv =
      ((X.skeletalSpectralSequence.iso r (r + 1) pq rfl hr).inv ⊗ₘ
        (Y.skeletalSpectralSequence.iso r (r + 1) pq' rfl hr).inv) ≫
        P.mixedPageHomologyPairTo r hr pq pq' t ht := by
  apply (cancel_mono (U.skeletalSpectralSequence.iso r (r + 1) t rfl hr).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [P.mixedPageHomologyPairTo_successor, tensorHom_comp_tensorHom_assoc]
  simp only [Iso.inv_hom_id, tensorHom_id, id_whiskerRight, Category.id_comp]

/-- Native cycle inclusions preserve mixed associativity and the original induced output cycle map. -/
theorem mixedPageCyclesPair_associativity
    (P : IntervalPairing X Y U) (Q : IntervalPairing U Z L)
    (R : IntervalPairing Y Z V) (T : IntervalPairing X V W) (γ : L ⟶ W)
    (r : ℤ) (hr : 1 ≤ r) (hassoc : mixedPageAssociativity P Q R T γ r hr)
    (pq pq' pq'' : ℤ × ℤ) :
    (P.pageCyclesPair r hr pq pq' ⊗ₘ 𝟙 (((Z.skeletalSpectralSequence).page r).cycles pq'')) ≫
      Q.mixedPageCyclesPairTo r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq'') ≫
      HomologicalComplex.cyclesMap (γ.spectralSequencePageMap skeletalPageCore r hr) (pq + (pq' + pq'')) =
    (α_ (((X.skeletalSpectralSequence).page r).cycles pq) (((Y.skeletalSpectralSequence).page r).cycles pq')
      (((Z.skeletalSpectralSequence).page r).cycles pq'')).hom ≫
      (𝟙 _ ⊗ₘ R.pageCyclesPair r hr pq' pq'') ≫ T.pageCyclesPair r hr pq (pq' + pq'') := by
  let AX := (X.skeletalSpectralSequence).page r
  let AY := (Y.skeletalSpectralSequence).page r
  let AZ := (Z.skeletalSpectralSequence).page r
  let AU := (U.skeletalSpectralSequence).page r
  let AV := (V.skeletalSpectralSequence).page r
  let AL := (L.skeletalSpectralSequence).page r
  let AW := (W.skeletalSpectralSequence).page r
  exact pairing_associativity_of_mono_projection
    (AX.iCycles pq) (AY.iCycles pq') (AZ.iCycles pq'')
    (AU.iCycles (pq + pq')) (AV.iCycles (pq' + pq''))
    (AL.iCycles (pq + (pq' + pq''))) (AW.iCycles (pq + (pq' + pq'')))
    (P.pageCyclesPair r hr pq pq')
    (Q.mixedPageCyclesPairTo r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq''))
    (R.pageCyclesPair r hr pq' pq'') (T.pageCyclesPair r hr pq (pq' + pq''))
    (P.pagePair r hr pq pq')
    (Q.pagePairTo r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq''))
    (R.pagePair r hr pq' pq'') (T.pagePair r hr pq (pq' + pq''))
    (HomologicalComplex.cyclesMap (γ.spectralSequencePageMap skeletalPageCore r hr) (pq + (pq' + pq'')))
    ((γ.spectralSequencePageMap skeletalPageCore r hr).f (pq + (pq' + pq'')))
    (P.pageCyclesPair_i r hr pq pq')
    (Q.mixedPageCyclesPairTo_i r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq''))
    (R.pageCyclesPair_i r hr pq' pq'') (T.pageCyclesPair_i r hr pq (pq' + pq''))
    (HomologicalComplex.cyclesMap_i _ _) (hassoc pq pq' pq'')

/-- Native homology quotients descend mixed associativity with the actual output homology map. -/
theorem mixedPageHomologyPair_associativity
    (P : IntervalPairing X Y U) (Q : IntervalPairing U Z L)
    (R : IntervalPairing Y Z V) (T : IntervalPairing X V W) (γ : L ⟶ W)
    (r : ℤ) (hr : 1 ≤ r) (hassoc : mixedPageAssociativity P Q R T γ r hr)
    (pq pq' pq'' : ℤ × ℤ) :
    (P.pageHomologyPair r hr pq pq' ⊗ₘ 𝟙 (((Z.skeletalSpectralSequence).page r).homology pq'')) ≫
      Q.mixedPageHomologyPairTo r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq'') ≫
      HomologicalComplex.homologyMap (γ.spectralSequencePageMap skeletalPageCore r hr) (pq + (pq' + pq'')) =
    (α_ (((X.skeletalSpectralSequence).page r).homology pq) (((Y.skeletalSpectralSequence).page r).homology pq')
      (((Z.skeletalSpectralSequence).page r).homology pq'')).hom ≫
      (𝟙 _ ⊗ₘ R.pageHomologyPair r hr pq' pq'') ≫ T.pageHomologyPair r hr pq (pq' + pq'') := by
  let AX := (X.skeletalSpectralSequence).page r
  let AY := (Y.skeletalSpectralSequence).page r
  let AZ := (Z.skeletalSpectralSequence).page r
  let AU := (U.skeletalSpectralSequence).page r
  let AV := (V.skeletalSpectralSequence).page r
  let AL := (L.skeletalSpectralSequence).page r
  let AW := (W.skeletalSpectralSequence).page r
  let : Epi (AX.homologyπ pq ⊗ₘ AY.homologyπ pq') := epi_tensorHom_of_preservesCokernels _ _
  let : Epi ((AX.homologyπ pq ⊗ₘ AY.homologyπ pq') ⊗ₘ AZ.homologyπ pq'') :=
    epi_tensorHom_of_preservesCokernels _ _
  exact pairing_associativity_of_epi_projection
    (AX.homologyπ pq) (AY.homologyπ pq') (AZ.homologyπ pq'')
    (AU.homologyπ (pq + pq')) (AV.homologyπ (pq' + pq''))
    (AL.homologyπ (pq + (pq' + pq''))) (AW.homologyπ (pq + (pq' + pq'')))
    (P.pageCyclesPair r hr pq pq')
    (Q.mixedPageCyclesPairTo r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq''))
    (R.pageCyclesPair r hr pq' pq'') (T.pageCyclesPair r hr pq (pq' + pq''))
    (P.pageHomologyPair r hr pq pq')
    (Q.mixedPageHomologyPairTo r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq''))
    (R.pageHomologyPair r hr pq' pq'') (T.pageHomologyPair r hr pq (pq' + pq''))
    (HomologicalComplex.cyclesMap (γ.spectralSequencePageMap skeletalPageCore r hr) (pq + (pq' + pq'')))
    (HomologicalComplex.homologyMap (γ.spectralSequencePageMap skeletalPageCore r hr) (pq + (pq' + pq'')))
    (P.pageHomologyPair_π r hr pq pq').symm
    (Q.mixedPageHomologyPairTo_π r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq'')).symm
    (R.pageHomologyPair_π r hr pq' pq'').symm (T.pageHomologyPair_π r hr pq (pq' + pq'')).symm
    (HomologicalComplex.homologyπ_naturality _ _).symm
    (mixedPageCyclesPair_associativity P Q R T γ r hr hassoc pq pq' pq'')

omit [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)] in
/-- The inverse native successor maps commute with the original output spectral-sequence map. -/
@[reassoc]
lemma spectralMap_successor_inv (γ : L ⟶ W) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
    (γ.spectralSequencePageMap skeletalPageCore (r + 1) (by omega)).f pq ≫
        (W.skeletalSpectralSequence.iso r (r + 1) pq rfl hr).inv =
      (L.skeletalSpectralSequence.iso r (r + 1) pq rfl hr).inv ≫
        HomologicalComplex.homologyMap (γ.spectralSequencePageMap skeletalPageCore r hr) pq := by
  apply (cancel_mono (W.skeletalSpectralSequence.iso r (r + 1) pq rfl hr).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Hom.spectralSequencePageMap_comm γ skeletalPageCore r (r + 1) pq rfl hr]
  simp only [Iso.inv_hom_id_assoc]

/-- Mixed page homology and the successor maps preserve mixed associativity. -/
theorem mixedPageAssociativity_successor
    (P : IntervalPairing X Y U) (Q : IntervalPairing U Z L)
    (R : IntervalPairing Y Z V) (T : IntervalPairing X V W) (γ : L ⟶ W)
    (r : ℤ) (hr : 1 ≤ r) (hassoc : mixedPageAssociativity P Q R T γ r hr) :
    mixedPageAssociativity P Q R T γ (r + 1) (by omega) := by
  intro pq pq' pq''
  let eX := X.skeletalSpectralSequence.iso r (r + 1) pq rfl hr
  let eY := Y.skeletalSpectralSequence.iso r (r + 1) pq' rfl hr
  let eZ := Z.skeletalSpectralSequence.iso r (r + 1) pq'' rfl hr
  let eU := U.skeletalSpectralSequence.iso r (r + 1) (pq + pq') rfl hr
  let eV := V.skeletalSpectralSequence.iso r (r + 1) (pq' + pq'') rfl hr
  let eL := L.skeletalSpectralSequence.iso r (r + 1) (pq + (pq' + pq'')) rfl hr
  let eW := W.skeletalSpectralSequence.iso r (r + 1) (pq + (pq' + pq'')) rfl hr
  exact pairing_associativity_of_mono_projection eX.inv eY.inv eZ.inv eU.inv eV.inv eL.inv eW.inv
    (P.pagePair (r + 1) (by omega) pq pq')
    (Q.pagePairTo (r + 1) (by omega) (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq''))
    (R.pagePair (r + 1) (by omega) pq' pq'') (T.pagePair (r + 1) (by omega) pq (pq' + pq''))
    (P.pageHomologyPair r hr pq pq')
    (Q.mixedPageHomologyPairTo r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq''))
    (R.pageHomologyPair r hr pq' pq'') (T.pageHomologyPair r hr pq (pq' + pq''))
    ((γ.spectralSequencePageMap skeletalPageCore (r + 1) (by omega)).f (pq + (pq' + pq'')))
    (HomologicalComplex.homologyMap (γ.spectralSequencePageMap skeletalPageCore r hr) (pq + (pq' + pq'')))
    (P.mixedPagePairTo_successor_inv r hr pq pq' (pq + pq') rfl)
    (Q.mixedPagePairTo_successor_inv r hr (pq + pq') pq'' (pq + (pq' + pq'')) (add_assoc pq pq' pq''))
    (R.mixedPagePairTo_successor_inv r hr pq' pq'' (pq' + pq'') rfl)
    (T.mixedPagePairTo_successor_inv r hr pq (pq' + pq'') (pq + (pq' + pq'')) rfl)
    (spectralMap_successor_inv γ r hr (pq + (pq' + pq'')))
    (mixedPageHomologyPair_associativity P Q R T γ r hr hassoc pq pq' pq'')

/-- Mixed associativity proved on an initial native page holds on every later integer page. -/
theorem mixedPageAssociativity_later
    (P : IntervalPairing X Y U) (Q : IntervalPairing U Z L)
    (R : IntervalPairing Y Z V) (T : IntervalPairing X V W) (γ : L ⟶ W)
    (r₀ : ℤ) (hr₀ : 1 ≤ r₀) (hassoc : mixedPageAssociativity P Q R T γ r₀ hr₀)
    (r : ℤ) (hr : r₀ ≤ r) : mixedPageAssociativity P Q R T γ r (by omega) := by
  let S : ℤ → Prop := fun s => ∀ hs : 1 ≤ s, mixedPageAssociativity P Q R T γ s hs
  have h : ∀ i : ℕ, S (r₀ + (i : ℤ)) := by
    intro i
    induction i with
    | zero => simpa only [Nat.cast_zero, add_zero] using (show S r₀ from fun _ => hassoc)
    | succ i ih =>
        have hs : S ((r₀ + (i : ℤ)) + 1) := by
          intro _
          exact mixedPageAssociativity_successor P Q R T γ (r₀ + (i : ℤ)) (by omega) (ih (by omega))
        exact (congrArg S (by omega : (r₀ + (i : ℤ)) + 1 = r₀ + ((i + 1 : ℕ) : ℤ))).mp hs
  have he : r₀ + ((r - r₀).toNat : ℤ) = r := by omega
  exact ((congrArg S he).mp (h (r - r₀).toNat)) (by omega)

end CategoryTheory.Abelian.SpectralObject.IntervalPairing
