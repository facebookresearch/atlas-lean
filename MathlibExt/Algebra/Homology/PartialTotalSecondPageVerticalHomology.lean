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

public import MathlibExt.Algebra.Homology.PartialTotalAdjacentCore
public import MathlibExt.Algebra.Homology.PartialTotalConnectingHorizontal
public import MathlibExt.Algebra.Homology.PartialTotalFirstPageDifferential
public import MathlibExt.Algebra.Homology.PartialTotalSignedRowHomology
public import MathlibExt.Algebra.Homology.VerticalHomologyComplex
public import MathlibExt.Algebra.Homology.HomotopyCategory.MappingConeCompHomology
public import MathlibExt.Algebra.Homology.Embedding.RestrictionHomology

/-!
# The second page as horizontal homology of vertical homology

Let `B` be a first-quadrant bicomplex in an abelian category. At fixed vertical degree `q`,
the first page of its partial-total spectral sequence is the horizontal complex with term
`H_q(B.X p)` and differential `ε(q) • H_q(B.d p p')`, where `ε(q) = (-1 : ℤˣ)^q`.

Multiplication by `ε(q)^p` in horizontal degree `p` identifies this signed complex with the
ordinary vertical-homology complex. Taking horizontal homology gives `E²_(p,q) ≅
H_p(B.verticalHomologyComplex q)` for every natural bidegree.

The first-page homology and second-page objects use the common spectral coordinate with
integer cuts `p - 2 ≤ p - 1 ≤ p ≤ p + 1` and middle cochain degree `-p - q`. The page-bound
data and neighboring-index identities specify the restriction maps, the cycle and homology
projections, and the degree-zero representative formula.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

private theorem partialTotalIsoInvHomEnd
    {D : Type*} [Category D] {A B X : D} (a : A ⟶ B) (e : X ≅ B) :
    (a ≫ e.inv) ≫ e.hom = a := by
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem partialTotalHomologyFunctorShiftObj
    {D : Type*} [Category D] [Abelian D] (K : CochainComplex D ℤ) (i : ℤ) :
    ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).shift i).obj K =
      K.homology i :=
  rfl

private def partialTotalShiftHomologyIso
    {D : Type*} [Category D] [Abelian D]
    (K : CochainComplex D ℤ) (n i i' : ℤ) (hi' : n + i = i') :
    (K⟦n⟧).homology i ≅ K.homology i' :=
  (eqToIso (partialTotalHomologyFunctorShiftObj (K⟦n⟧) i)).symm ≪≫
    ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).shiftIso
      n i i' hi').app K ≪≫
    eqToIso (partialTotalHomologyFunctorShiftObj K i')

private theorem partialTotalIsoTransportEq
    {D : Type*} [Category D] {A B₀ C₀ B₁ C₁ : D}
    (s : B₀ ≅ C₀) (eS : B₀ ≅ B₁) (eT : C₀ ≅ C₁)
    {f : A ⟶ B₀} {g : A ⟶ C₀} (h : f = g ≫ s.inv) :
    f ≫ eS.hom = (g ≫ eT.hom) ≫ (eS.symm ≪≫ s ≪≫ eT).inv := by
  calc
    f ≫ eS.hom = (g ≫ s.inv) ≫ eS.hom :=
      congrArg (fun k : A ⟶ B₀ => k ≫ eS.hom) h
    _ = (g ≫ eT.hom) ≫ (eS.symm ≪≫ s ≪≫ eT).inv := by
      simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]

private theorem partialTotalShiftMapHomology
    {D : Type*} [Category D] [Abelian D]
    {K L : CochainComplex D ℤ} {n : ℤ} (z : K ⟶ L⟦n⟧)
    (i i' : ℤ) (hi' : n + i = i') :
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).shiftMap z i i' hi' =
      HomologicalComplex.homologyMap z i ≫
        (partialTotalShiftHomologyIso L n i i' hi').hom := by
  let s :=
    ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).shiftIso
      n i i' hi').app L
  change HomologicalComplex.homologyMap z i ≫ s.hom =
    HomologicalComplex.homologyMap z i ≫
      (𝟙 ((L⟦n⟧).homology i) ≫ s.hom ≫ 𝟙 (L.homology i'))
  rw [Category.id_comp, Category.comp_id]

private theorem partialTotalLiftCyclesShiftHomology
    {D : Type*} [Category D] [Abelian D]
    (K : CochainComplex D ℤ) {A : D} {n i : ℤ} (f : A ⟶ (K⟦n⟧).X i)
    (j : ℤ) (hj : (ComplexShape.up ℤ).next i = j)
    (hf : f ≫ (K⟦n⟧).d i j = 0) (i' : ℤ) (hi' : n + i = i')
    (j' : ℤ) (hj' : (ComplexShape.up ℤ).next i' = j') :
    ∃ hy : (f ≫ (K.shiftFunctorObjXIso n i i' (by omega)).hom) ≫ K.d i' j' = 0,
      (K⟦n⟧).liftCycles f j hj hf ≫ (K⟦n⟧).homologyπ i ≫
          (partialTotalShiftHomologyIso K n i i' hi').hom =
        K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by omega)).hom) j' hj' hy ≫
          K.homologyπ i' := by
  have hy : (f ≫ (K.shiftFunctorObjXIso n i i' (by omega)).hom) ≫ K.d i' j' = 0 := by
    simp only [CochainComplex.next] at hj hj'
    obtain rfl : i' = i + n := by omega
    obtain rfl : j' = j + n := by omega
    dsimp at hf ⊢
    simp only [Linear.comp_units_smul] at hf
    apply (one_smul (M := ℤˣ) _).symm.trans _
    rw [← Int.units_mul_self n.negOnePow, mul_smul, Category.comp_id, hf, smul_zero]
  let s :=
    ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).shiftIso
      n i i' hi').app K
  let eS := eqToIso (partialTotalHomologyFunctorShiftObj (K⟦n⟧) i)
  let eT := eqToIso (partialTotalHomologyFunctorShiftObj K i')
  let E := partialTotalShiftHomologyIso K n i i' hi'
  let f₀ : A ⟶
      (shiftFunctor (CochainComplex D ℤ) n ⋙
        (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).shift i).obj K :=
    (K⟦n⟧).liftCycles f j hj hf ≫ (K⟦n⟧).homologyπ i ≫ eS.inv
  let g₀ : A ⟶
      ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).shift i').obj K :=
    K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by omega)).hom) j' hj' hy ≫
      K.homologyπ i' ≫ eT.inv
  have hnative : f₀ = g₀ ≫ s.inv := by
    change (K⟦n⟧).liftCycles f j hj hf ≫
        (K⟦n⟧).homologyπ i ≫ 𝟙 ((K⟦n⟧).homology i) =
      (K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by omega)).hom)
          j' hj' hy ≫ K.homologyπ i' ≫ 𝟙 (K.homology i')) ≫ s.inv
    rw [Category.comp_id, Category.comp_id, Category.assoc]
    exact CochainComplex.liftCycles_shift_homologyπ K f j hj hf i' hi' j' hj'
  have htransport := partialTotalIsoTransportEq s eS eT hnative
  change f₀ ≫ eS.hom = (g₀ ≫ eT.hom) ≫ E.inv at htransport
  have hS :
      f₀ ≫ eS.hom = (K⟦n⟧).liftCycles f j hj hf ≫ (K⟦n⟧).homologyπ i := by
    simpa only [f₀, Category.assoc] using
      partialTotalIsoInvHomEnd
        ((K⟦n⟧).liftCycles f j hj hf ≫ (K⟦n⟧).homologyπ i) eS
  have hT :
      g₀ ≫ eT.hom =
        K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by omega)).hom) j' hj' hy ≫
          K.homologyπ i' := by
    simpa only [g₀, Category.assoc] using
      partialTotalIsoInvHomEnd
        (K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by omega)).hom) j' hj' hy ≫
          K.homologyπ i') eT
  have hnormalized :
      (K⟦n⟧).liftCycles f j hj hf ≫ (K⟦n⟧).homologyπ i =
        (K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by omega)).hom) j' hj' hy ≫
          K.homologyπ i') ≫ E.inv :=
    hS.symm.trans (htransport.trans
      (congrArg (fun t : A ⟶ K.homology i' => t ≫ E.inv) hT))
  have hfinal :
      ((K⟦n⟧).liftCycles f j hj hf ≫ (K⟦n⟧).homologyπ i) ≫ E.hom =
        K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by omega)).hom) j' hj' hy ≫
          K.homologyπ i' :=
    (congrArg (fun t : A ⟶ (K⟦n⟧).homology i => t ≫ E.hom) hnormalized).trans
      (partialTotalIsoInvHomEnd
        (K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by omega)).hom) j' hj' hy ≫
          K.homologyπ i') E)
  refine ⟨hy, ?_⟩
  simpa only [E, Category.assoc] using hfinal

private theorem partialTotalCycleCoordinateComm
    {D : Type*} [Category D] [Preadditive D]
    {A L M Z : D} (s : ℤˣ) {u v : A ⟶ Z} (hc : u = s • v)
    (a : A ⟶ L) (b : A ⟶ M) (f : M ⟶ L) (i : L ⟶ Z) [Mono i]
    (ha : a ≫ i = u) (hb : b ≫ f ≫ i = v) : a = s • (b ≫ f) := by
  have hb' : (b ≫ f) ≫ i = v := (Category.assoc _ _ _).trans hb
  apply (cancel_mono i).1
  calc
    a ≫ i = u := ha
    _ = s • v := hc
    _ = s • ((b ≫ f) ≫ i) :=
      congrArg (fun t : A ⟶ Z => s • t) hb'.symm
    _ = (s • (b ≫ f)) ≫ i :=
      (Linear.units_smul_comp s (b ≫ f) i).symm

private theorem partialTotalSignedRowXHom (p q : ℕ) :
    eqToHom (HomologicalComplex₂.signedRow_X B p q) = 𝟙 ((B.X p).X q) := by
  rfl

private theorem partialTotalIsoCancelTail
    {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ X₅ : D}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (e : X₃ ≅ X₂)
    (f : X₂ ⟶ X₄) (g : X₄ ⟶ X₅) :
    ((a ≫ b ≫ e.inv) ≫ e.hom) ≫ f ≫ g = a ≫ b ≫ f ≫ g := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem partialTotalHomologyFactors_inv_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.app K ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
          HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map f =
      HomologicalComplex.homologyMap f n ≫
        (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.app L := by
  simpa only [HomologicalComplex.homologyFunctor_map] using
    ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.naturality f).symm

private theorem partialTotalHomologyFactors_hom_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map f ≫
        (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.app L =
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.app K ≫
        HomologicalComplex.homologyMap f n := by
  simpa only [HomologicalComplex.homologyFunctor_map] using
    (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.naturality f

private theorem partialTotalConeSpectralHMap
    {D E : ComposableArrows (CochainComplex C ℤ) 1} (φ : D ⟶ E) (n : ℤ) :
    (((HomotopyCategory.spectralObjectMappingCone C).mapHomologicalFunctor
        (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)).H n).map φ =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map
          ((HomotopyCategory.composableArrowsFunctor C).map φ) := rfl

private theorem partialTotalSpectralδ_precompose
    {J : Type*} [Category J] (Y : CategoryTheory.Abelian.SpectralObject C J)
    {i j k i' j' k' a b : J}
    (f : i ⟶ j) (g : j ⟶ k) (f' : i' ⟶ j') (g' : j' ⟶ k')
    (α : ComposableArrows.mk₁ f ⟶ ComposableArrows.mk₁ f')
    (β : ComposableArrows.mk₁ g ⟶ ComposableArrows.mk₁ g') {c : a ⟶ b}
    (s : ComposableArrows.mk₁ c ⟶ ComposableArrows.mk₁ g)
    (t : ComposableArrows.mk₁ c ⟶ ComposableArrows.mk₁ g') (ht : t = s ≫ β)
    (n n' : ℤ) (hαβ : α.app 1 = β.app 0) (hn : n + 1 = n') :
    (Y.H n).map s ≫ Y.δ f g n n' hn ≫ (Y.H n').map α =
      (Y.H n).map t ≫ Y.δ f' g' n n' hn := by
  have hδ := Y.δ_naturality f g f' g' α β n n' hαβ hn
  have h := congrArg
    (fun z : (Y.H n).obj (ComposableArrows.mk₁ g) ⟶
        (Y.H n').obj (ComposableArrows.mk₁ f') => (Y.H n).map s ≫ z) hδ.symm
  simpa only [ht, Functor.map_comp, Category.assoc] using h

omit [Abelian C] in
private theorem partialTotalTransportHomEquality
    {ι : Type*} {X Y : ι → C} (f g : ∀ i, X i ⟶ Y i)
    {i j : ι} (h : i = j) (hj : f j = g j) : f i = g i := by
  subst j
  exact hj

private theorem partialTotalMapEqToIso
    {D E : Type*} [Category D] [Category E] (F : D ⥤ E) {X Y : D} (h : X = Y) :
    F.mapIso (eqToIso h) = eqToIso (congrArg F.obj h) := by
  subst Y
  apply Iso.ext
  simp

private theorem partialTotalEqTransportConjugation
    {D : Type*} [Category D] {A A' M N : D}
    (hA : A = M) (hA' : A' = M) (hAA' : A = A') (e : M ≅ N) :
    (eqToIso hA ≪≫ e).symm ≪≫ eqToIso hAA' ≪≫ (eqToIso hA' ≪≫ e) =
      Iso.refl N := by
  subst A
  subst A'
  apply Iso.ext
  simp

private theorem partialTotalPrePostNaturality
    {D : Type*} [Category D] {X Y A B₀ B₁ Z C₀ U V W : D}
    (pre : X ⟶ A) (post : Z ⟶ Y)
    {s₀ : A ⟶ B₀} {δ₀ : B₀ ⟶ B₁} {s₂ : B₁ ⟶ Z}
    {t₀ : A ⟶ C₀} {δ₁ : C₀ ⟶ Z}
    {u₀ : X ⟶ U} {u₁ : U ⟶ B₀} {v₀ : B₁ ⟶ V} {v₁ : V ⟶ Y}
    {w₀ : X ⟶ W} {w₁ : W ⟶ C₀}
    (hpre : pre ≫ s₀ = u₀ ≫ u₁) (hpost : s₂ ≫ post = v₀ ≫ v₁)
    (ht : pre ≫ t₀ = w₀ ≫ w₁) (h : s₀ ≫ δ₀ ≫ s₂ = t₀ ≫ δ₁) :
    u₀ ≫ u₁ ≫ δ₀ ≫ v₀ ≫ v₁ = w₀ ≫ w₁ ≫ δ₁ ≫ post := by
  have h' : pre ≫ s₀ ≫ δ₀ ≫ s₂ ≫ post = pre ≫ t₀ ≫ δ₁ ≫ post := by
    simpa only [Category.assoc] using
      congrArg (fun k : A ⟶ Z => pre ≫ k ≫ post) h
  rw [reassoc_of% hpre, hpost, reassoc_of% ht] at h'
  exact h'

private theorem partialTotalFourSandwichEq
    {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : D}
    {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃}
    {f₃ : X₃ ⟶ X₄} {f₄ : X₄ ⟶ X₅} {f₅ : X₅ ⟶ X₆} {k : X₀ ⟶ X₆}
    (h : f₀ ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ = k) :
    (f₀ ≫ (f₁ ≫ f₂ ≫ f₃ ≫ f₄)) ≫ f₅ = k := by
  simpa only [Category.assoc] using h

private theorem partialTotalThreePostEq
    {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ : D}
    {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃}
    {f₃ : X₃ ⟶ X₄} {k : X₀ ⟶ X₄}
    (h : f₀ ≫ f₁ ≫ f₂ ≫ f₃ = k) :
    (f₀ ≫ (f₁ ≫ f₂)) ≫ f₃ = k := by
  simpa only [Category.assoc] using h

private theorem partialTotalFourMiddleEq
    {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : D}
    {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃}
    {f₃ : X₃ ⟶ X₄} {f₄ : X₄ ⟶ X₅} {f₅ : X₅ ⟶ X₆} {k : X₀ ⟶ X₆}
    (h : f₀ ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ = k) :
    f₀ ≫ (f₁ ≫ f₂ ≫ f₃ ≫ f₄) ≫ f₅ = k := by
  simpa only [Category.assoc] using h

private theorem partialTotalLeftIdentityEq
    {D : Type*} [Category D] {X Y : D}
    (a : X ⟶ X) (f : X ⟶ Y) (ha : a = 𝟙 X) : f = a ≫ f := by
  rw [ha, Category.id_comp]

private theorem partialTotalSourceCoordinateEq
    {D : Type*} [Category D] {X A B C₀ U V W : D}
    {s : X ⟶ A} {p : A ⟶ B} {g g₀ : B ⟶ C₀}
    {hm : X ⟶ U} {fac : U ⟶ A} {inv : X ⟶ V} {step : V ⟶ A}
    {a : A ⟶ W} {b : W ⟶ B} {u : V ⟶ C₀} {k : X ⟶ C₀}
    (hs : s = hm ≫ fac) (hp : p = a ≫ b) (hg : g = g₀)
    (hnat : hm ≫ fac = inv ≫ step)
    (hu : step ≫ a ≫ b ≫ g₀ = u) (hk : inv ≫ u = k) :
    s ≫ p ≫ g = k := by
  rw [hs, hp, hg]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, hu]
  exact hk

private theorem partialTotalTargetCoordinateEq
    {D : Type*} [Category D] {X A B C₀ Y : D}
    {map : X ⟶ A} {t : A ⟶ Y} {fac : A ⟶ B} {post : B ⟶ Y}
    {fac₀ : X ⟶ C₀} {bridge : C₀ ⟶ B} {target : C₀ ⟶ Y}
    (ht : t = fac ≫ post) (hnat : map ≫ fac = fac₀ ≫ bridge)
    (hc : bridge ≫ post = target) : map ≫ t = fac₀ ≫ target := by
  rw [ht, ← Category.assoc, hnat, Category.assoc, hc]

private theorem partialTotalConjugateCoordinatesEq
    {D : Type*} [Category D] {X A B C₀ Y U V S T : D}
    {a : X ⟶ A} {b : A ⟶ B} {c : B ⟶ C₀} {d : C₀ ⟶ Y}
    {u : B ⟶ U} {delta delta₀ : U ⟶ V} {v : V ⟶ C₀}
    {s₀ : X ⟶ S} {s₁ : S ⟶ U} {t₀ : V ⟶ T} {t₁ : T ⟶ Y}
    {k : X ⟶ Y}
    (hc : c = u ≫ delta ≫ v) (hs : a ≫ b ≫ u = s₀ ≫ s₁)
    (ht : v ≫ d = t₀ ≫ t₁) (hdelta : delta = delta₀)
    (hk : s₀ ≫ s₁ ≫ delta₀ ≫ t₀ ≫ t₁ = k) :
    a ≫ b ≫ c ≫ d = k := by
  rw [hc, hdelta]
  simp only [Category.assoc]
  rw [reassoc_of% hs, ht]
  exact hk

private theorem partialTotalSevenReassoc
    {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : D}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄)
    (e : X₄ ⟶ X₅) (f : X₅ ⟶ X₆) (g : X₆ ⟶ X₇) :
    (a ≫ b) ≫ (c ≫ d) ≫ e ≫ (f ≫ g) = a ≫ b ≫ c ≫ d ≫ e ≫ f ≫ g := by
  simp only [Category.assoc]

private theorem partialTotalSignedCoordinateSquare
    {D : Type*} [Category D] [Preadditive D] [Linear ℤ D]
    {A₀ A₁ B₀ B₁ C₀ C₁ : D}
    (u : ℤˣ) (h : A₀ ⟶ A₁) (e₀ : A₀ ≅ B₀) (e₁ : A₁ ≅ B₁)
    (r₀ : B₀ ⟶ C₀) (r₁ : B₁ ⟶ C₁) (f : B₀ ⟶ B₁) (g : C₀ ⟶ C₁)
    (hh : h ≫ e₁.hom = u • (e₀.hom ≫ f)) (hf : f ≫ r₁ = r₀ ≫ g) :
    h ≫ (e₁.hom ≫ r₁) = (e₀.hom ≫ r₀) ≫ (u • g) := by
  calc
    h ≫ (e₁.hom ≫ r₁) = (u • (e₀.hom ≫ f)) ≫ r₁ := by
      rw [← Category.assoc, hh]
    _ = u • ((e₀.hom ≫ f) ≫ r₁) := by
      change ((u : ℤ) • (e₀.hom ≫ f)) ≫ r₁ =
        (u : ℤ) • ((e₀.hom ≫ f) ≫ r₁)
      exact Preadditive.zsmul_comp (f := e₀.hom ≫ f) (g := r₁) (u : ℤ)
    _ = u • ((e₀.hom ≫ r₀) ≫ g) := by
      congr 1
      rw [Category.assoc, hf, ← Category.assoc]
    _ = (e₀.hom ≫ r₀) ≫ (u • g) := by
      change (u : ℤ) • ((e₀.hom ≫ r₀) ≫ g) =
        (e₀.hom ≫ r₀) ≫ ((u : ℤ) • g)
      exact (Preadditive.comp_zsmul (f := e₀.hom ≫ r₀) (g := g) (u : ℤ)).symm

private theorem partialTotalIsoCoordinateComm
    {D : Type*} [Category D] {A₀ A₁ B₀ B₁ C₀ C₁ : D}
    (e₀ : A₀ ≅ B₀) (e₁ : A₁ ≅ B₁) (r₀ : B₀ ≅ C₀) (r₁ : B₁ ≅ C₁)
    (f : B₀ ⟶ B₁) (g : C₀ ⟶ C₁) (h : f ≫ r₁.hom = r₀.hom ≫ g) :
    (e₀.hom ≫ r₀.hom) ≫ g =
      (e₀.hom ≫ f ≫ e₁.inv) ≫ (e₁.hom ≫ r₁.hom) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun k : B₀ ⟶ C₁ => e₀.hom ≫ k) h.symm

private theorem partialTotalConeCoordinateCollapse
    {D : Type*} [Category D] {A B C₀ D₀ E F G H : D}
    (a : A ⟶ B) (b : B ⟶ C₀) (z : C₀ ⟶ D₀) (t : D₀ ⟶ H)
    (dT : D₀ ⟶ G) (r₀ : G ⟶ H) (s : C₀ ⟶ F) (g : F ⟶ G)
    (dR : C₀ ⟶ E) (δR : E ⟶ F) (dS : B ⟶ E) (r₁ : A ⟶ E)
    (ht : t = dT ≫ r₀) (hz : z ≫ dT = s ≫ g) (hs : s = dR ≫ δR)
    (hb : b ≫ dR = dS) (ha : a ≫ dS = r₁) :
    a ≫ b ≫ z ≫ t = r₁ ≫ δR ≫ g ≫ r₀ := by
  rw [ht]
  rw [reassoc_of% hz, hs]
  simp only [Category.assoc]
  rw [reassoc_of% hb, reassoc_of% ha]

private theorem partialTotalUnfoldMiddleThreeEq
    {D : Type*} [Category D] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : D}
    {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃}
    {f₃ : X₃ ⟶ X₄} {f₄ : X₄ ⟶ X₅} {f₅ : X₅ ⟶ X₆} {k : X₀ ⟶ X₆}
    (h : f₀ ≫ f₁ ≫ (f₂ ≫ f₃ ≫ f₄) ≫ f₅ = k) :
    f₀ ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ = k := by
  simpa only [Category.assoc] using h

/-- Fixed vertical degree as a first-page chain shape.

For a natural vertical degree `q`, the map `p ↦ (p, q)` embeds the natural homological chain
shape in the first-page shape `(-1, 0)`. It identifies the horizontal arrows at fixed `q` with
the first-page differential arrows. -/
def partialTotalFirstPageRowEmbedding (q : ℕ) :
    (ComplexShape.down ℕ).Embedding
      (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩) :=
  ComplexShape.Embedding.mk'
    (ComplexShape.down ℕ)
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩)
    (fun p => (p, q))
    (fun _ _ h => by simpa using congrArg Prod.fst h)
    (fun p p' => by
      simp only [ComplexShape.spectralSequenceNat_rel_iff]
      constructor
      · intro h
        change p' + 1 = p at h
        constructor <;> omega
      · rintro ⟨h, _⟩
        change p' + 1 = p
        omega)

/-- Index formula for the first-page row embedding.

The row embedding at vertical degree `q` sends horizontal degree `p` to the bidegree `(p, q)`. -/
@[simp]
theorem partialTotalFirstPageRowEmbedding_f (p q : ℕ) :
    (partialTotalFirstPageRowEmbedding q).f p = (p, q) :=
  rfl

instance (q : ℕ) : (partialTotalFirstPageRowEmbedding q).IsRelIff where
  rel' p p' h := by
    change (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).Rel
      (p, q) (p', q) at h
    change p' + 1 = p
    have hfst : (p : ℤ) + (-1 : ℤ) = p' :=
      ((ComplexShape.spectralSequenceNat_rel_iff
        ⟨(-1 : ℤ), 0⟩ (p, q) (p', q)).mp h).1
    omega

private noncomputable def partialTotalE₁MiddleTransportIso (m q : ℕ) :
    B.partialTotalCochainFiltration.obj ((core).i₂ (m, q)) ≅
      B.partialTotalCochainFiltration.obj ((core).i₁ (m + 1, q)) := by
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  exact eqToIso (congrArg B.partialTotalCochainFiltration.obj hmid)

private noncomputable def partialTotalE₁MiddleTransportRawIso (m q : ℕ) :
    B.partialTotalEIntFiltration.obj ((core).i₂ (m, q)) ≅
      B.partialTotalEIntFiltration.obj ((core).i₁ (m + 1, q)) := by
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  exact eqToIso (congrArg B.partialTotalEIntFiltration.obj hmid)

private theorem partialTotalE₁_middle_iso_raw (m q : ℕ) :
    let e₀ := B.partialTotalE₁StepIso m q
    let e₁ := B.partialTotalE₁StepIso (m + 1) q
    let t := B.partialTotalE₁MiddleTransportRawIso m q
    let eA :
        (B.partialTotalStepShortComplex (m + 1)).X₁ ≅
          (B.partialTotalStepShortComplex m).X₂ :=
      eqToIso (by
        rw [B.partialTotalStepShortComplex_X₁_succ,
          B.partialTotalStepShortComplex_X₂])
    (e₀.app 1).symm ≪≫ t ≪≫ e₁.app 0 = eA.symm := by
  dsimp only
  cases m with
  | zero =>
    let hU : B.partialTotalEIntFiltration.obj ((core).i₂ (0, q)) =
        B.partialTotalEIntFiltration.obj (((0 : ℕ) : ℤ) : EInt) :=
      congrArg B.partialTotalEIntFiltration.obj (by simp)
    let hL : B.partialTotalEIntFiltration.obj ((core).i₁ (0 + 1, q)) =
        B.partialTotalEIntFiltration.obj (((0 : ℕ) : ℤ) : EInt) :=
      congrArg B.partialTotalEIntFiltration.obj (by simp)
    let hM := hU.trans hL.symm
    change
      (eqToIso hU ≪≫ B.partialTotalEIntFiltrationObjIso 0).symm ≪≫
          eqToIso hM ≪≫ (eqToIso hL ≪≫ B.partialTotalEIntFiltrationObjIso 0) =
        Iso.refl (B.partialTotal 0)
    exact partialTotalEqTransportConjugation hU hL hM
      (B.partialTotalEIntFiltrationObjIso 0)
  | succ m =>
    let hU : B.partialTotalEIntFiltration.obj ((core).i₂ (m + 1, q)) =
        B.partialTotalEIntFiltration.obj (((m + 1 : ℕ) : ℤ) : EInt) :=
      congrArg B.partialTotalEIntFiltration.obj (by simp)
    let hL : B.partialTotalEIntFiltration.obj ((core).i₁ (m + 1 + 1, q)) =
        B.partialTotalEIntFiltration.obj (((m + 1 : ℕ) : ℤ) : EInt) :=
      congrArg B.partialTotalEIntFiltration.obj (by simp)
    let hM := hU.trans hL.symm
    change
      (eqToIso hU ≪≫ B.partialTotalEIntFiltrationObjIso (m + 1)).symm ≪≫
          eqToIso hM ≪≫ (eqToIso hL ≪≫ B.partialTotalEIntFiltrationObjIso (m + 1)) =
        Iso.refl (B.partialTotal (m + 1))
    exact partialTotalEqTransportConjugation hU hL hM
      (B.partialTotalEIntFiltrationObjIso (m + 1))

private theorem partialTotalE₁CochainStepIso_app_one (p q : ℕ) :
    (B.partialTotalE₁CochainStepIso p q).app 1 =
      (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
        ((B.partialTotalE₁StepIso p q).app 1) := by
  let F : ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
    ComplexShape.embeddingDownNat.extendFunctor C
  apply Iso.ext
  dsimp only [partialTotalE₁CochainStepIso,
    CategoryTheory.Functor.mapComposableArrowsObjMk₁Iso]
  change (𝟙 _ ≫ F.map ((B.partialTotalE₁StepIso p q).app 1).hom ≫ 𝟙 _) =
    F.map ((B.partialTotalE₁StepIso p q).app 1).hom
  simp only [Category.id_comp, Category.comp_id]

private theorem partialTotalE₁CochainStepIso_app_zero (p q : ℕ) :
    (B.partialTotalE₁CochainStepIso p q).app 0 =
      (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
        ((B.partialTotalE₁StepIso p q).app 0) := by
  let F : ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
    ComplexShape.embeddingDownNat.extendFunctor C
  apply Iso.ext
  dsimp only [partialTotalE₁CochainStepIso,
    CategoryTheory.Functor.mapComposableArrowsObjMk₁Iso]
  change (𝟙 _ ≫ F.map ((B.partialTotalE₁StepIso p q).app 0).hom ≫ 𝟙 _) =
    F.map ((B.partialTotalE₁StepIso p q).app 0).hom
  simp only [Category.id_comp, Category.comp_id]

private theorem partialTotalE₁MiddleTransportIso_eq_mapIso (m q : ℕ) :
    B.partialTotalE₁MiddleTransportIso m q =
      (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
      (B.partialTotalE₁MiddleTransportRawIso m q) := by
  let F : ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
    ComplexShape.embeddingDownNat.extendFunctor C
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  let hraw : B.partialTotalEIntFiltration.obj ((core).i₂ (m, q)) =
      B.partialTotalEIntFiltration.obj ((core).i₁ (m + 1, q)) :=
    congrArg B.partialTotalEIntFiltration.obj hmid
  dsimp only [partialTotalE₁MiddleTransportIso,
    partialTotalE₁MiddleTransportRawIso]
  change eqToIso (congrArg F.obj hraw) = F.mapIso (eqToIso hraw)
  exact (partialTotalMapEqToIso F hraw).symm

private theorem partialTotalE₁_middle_iso (m q : ℕ) :
    let e₀ := B.partialTotalE₁CochainStepIso m q
    let e₁ := B.partialTotalE₁CochainStepIso (m + 1) q
    let t := B.partialTotalE₁MiddleTransportIso m q
    let eA := B.partialTotalAdjacentStepCochainIso m
    (e₀.app 1).symm ≪≫ t ≪≫ e₁.app 0 = eA.symm := by
  let F : ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
    ComplexShape.embeddingDownNat.extendFunctor C
  dsimp only
  rw [B.partialTotalE₁CochainStepIso_app_one m q,
    B.partialTotalE₁MiddleTransportIso_eq_mapIso m q,
    B.partialTotalE₁CochainStepIso_app_zero (m + 1) q]
  dsimp only [partialTotalAdjacentStepCochainIso]
  have hStep :
      (B.partialTotalStepShortComplex (m + 1)).X₁ =
        (B.partialTotalStepShortComplex m).X₂ :=
    (B.partialTotalStepShortComplex_X₁_succ m).trans
      (B.partialTotalStepShortComplex_X₂ m).symm
  change
    (F.mapIso ((B.partialTotalE₁StepIso m q).app 1)).symm ≪≫
        F.mapIso (B.partialTotalE₁MiddleTransportRawIso m q) ≪≫
        F.mapIso ((B.partialTotalE₁StepIso (m + 1) q).app 0) =
      (F.mapIso (eqToIso hStep)).symm
  simpa only [Functor.mapIso_symm, Functor.mapIso_trans] using
    congrArg F.mapIso (B.partialTotalE₁_middle_iso_raw m q)

private theorem partialTotalE₁CoreSuccessorMap_eq (m q : ℕ) :
    B.partialTotalE₁CoreSuccessorMap m q =
      (B.partialTotalE₁MiddleTransportIso m q).hom ≫
        B.partialTotalCochainFiltration.map
          (homOfLE ((core).le₁₂ (m + 1, q))) := by
  let F := B.partialTotalCochainFiltration
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  dsimp only [partialTotalE₁CoreSuccessorMap,
    partialTotalE₁MiddleTransportIso]
  change F.map _ = eqToHom (congrArg F.obj hmid) ≫ F.map _
  rw [← eqToHom_map F hmid, ← F.map_comp]
  apply F.congr_map
  subsingleton

/-- Adjacent first-page map through the partial-total short complex.

For natural `m` and `q`, the adjacent cochain map used for the first-page differential is the
inverse adjacent-step cochain isomorphism followed by the first map of the step short complex
at stage `m + 1`. -/
theorem partialTotalE₁AdjacentCochainMap_eq (m q : ℕ) :
    B.partialTotalE₁AdjacentCochainMap m q =
      (B.partialTotalAdjacentStepCochainIso m).inv ≫
        (B.partialTotalStepCochainShortComplex (m + 1)).f := by
  let e₀ := B.partialTotalE₁CochainStepIso m q
  let e₁ := B.partialTotalE₁CochainStepIso (m + 1) q
  let t : B.partialTotalCochainFiltration.obj ((core).i₂ (m, q)) ≅
      B.partialTotalCochainFiltration.obj ((core).i₁ (m + 1, q)) :=
    B.partialTotalE₁MiddleTransportIso m q
  let eA : (B.partialTotalStepCochainShortComplex (m + 1)).X₁ ≅
      (B.partialTotalStepCochainShortComplex m).X₂ := B.partialTotalAdjacentStepCochainIso m
  have hmidIso := B.partialTotalE₁_middle_iso m q
  have hmid : (e₀.app 1).inv ≫ t.hom ≫ (e₁.app 0).hom = eA.inv := by
    change ((e₀.app 1).symm ≪≫ t ≪≫ e₁.app 0).hom = eA.symm.hom
    exact congrArg Iso.hom hmidIso
  have hcore := B.partialTotalE₁CoreSuccessorMap_eq m q
  dsimp only [partialTotalE₁AdjacentCochainMap]
  rw [hcore]
  calc
    (e₀.app 1).inv ≫
          (t.hom ≫ B.partialTotalCochainFiltration.map
            (homOfLE ((core).le₁₂ (m + 1, q)))) ≫
          (e₁.app 1).hom =
        ((e₀.app 1).inv ≫ t.hom ≫ (e₁.app 0).hom) ≫
          (B.partialTotalStepCochainShortComplex (m + 1)).f := by
            have hnat :
                B.partialTotalCochainFiltration.map
                (homOfLE ((core).le₁₂ (m + 1, q))) ≫
                  (e₁.app 1).hom =
              (e₁.app 0).hom ≫
                (B.partialTotalStepCochainShortComplex (m + 1)).f := by
              exact ComposableArrows.naturality' e₁.hom 0 1
            have hnat' := congrArg
              (fun f => (e₀.app 1).inv ≫ t.hom ≫ f) hnat
            simpa only [Category.assoc] using hnat'
    _ = eA.inv ≫
          (B.partialTotalStepCochainShortComplex (m + 1)).f := by
            rw [hmid]

private theorem mappingCone_shiftMap_eq_shortExact
    (R : ShortComplex (CochainComplex C ℤ))
    (hR : R.ShortExact) (n n' : ℤ) (h : n + 1 = n') :
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle R.f).mor₃ n n' (by omega) =
      HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.descShortComplex R) n ≫
        hR.δ n n' h := by
  let e₀ : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj
        (CochainComplex.mappingCone R.f) ≅ (CochainComplex.mappingCone R.f).homology n :=
    (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).app
      (CochainComplex.mappingCone R.f)
  let e₁ : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n').obj R.X₁ ≅
        R.X₁.homology n' :=
    (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n').app R.X₁
  let δ : (CochainComplex.mappingCone R.f).homology n ⟶ R.X₁.homology n' :=
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (CochainComplex.mappingCone.triangle R.f).mor₃ n n' (by omega)
  let δh : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj
        (CochainComplex.mappingCone R.f) ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n').obj R.X₁ :=
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
      (CochainComplex.mappingCone.triangleh R.f) n n' h
  let desc : (CochainComplex.mappingCone R.f).homology n ⟶ R.X₃.homology n :=
    HomologicalComplex.homologyMap (CochainComplex.mappingCone.descShortComplex R) n
  let δR : R.X₃.homology n ⟶ R.X₁.homology n' := hR.δ n n' h
  have hq : δh = e₀.hom ≫ δ ≫ e₁.inv :=
    CochainComplex.homologySequenceδ_quotient_mapTriangle_obj
      (CochainComplex.mappingCone.triangle R.f) n n' h
  have hs : δh = e₀.hom ≫ desc ≫ δR ≫ e₁.inv :=
    CochainComplex.mappingCone.homologySequenceδ_triangleh hR n n' h
  change δ = desc ≫ δR
  apply (cancel_epi e₀.hom).1
  apply (cancel_mono e₁.inv).1
  simpa only [Category.assoc] using hq.symm.trans hs

private theorem mappingCone_homologySequenceδ_normalized
    (S : ShortComplex (CochainComplex C ℤ))
    {X : CochainComplex C ℤ} (g : S.X₂ ⟶ X)
    (n n' : ℤ) (h : n + 1 = n') :
    (HomotopyCategory.homologyFunctorFactors
        C (ComplexShape.up ℤ) n).inv.app
          (CochainComplex.mappingCone g) ≫
      (HomotopyCategory.homologyFunctor C
        (ComplexShape.up ℤ) 0).homologySequenceδ
          (CochainComplex.mappingConeCompTriangleh S.f g) n n' h ≫
      (HomotopyCategory.homologyFunctorFactors
        C (ComplexShape.up ℤ) n').hom.app
          (CochainComplex.mappingCone S.f) ≫
      HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.descShortComplex S) n' =
    (HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) 0).shiftMap
          (CochainComplex.mappingCone.triangle g).mor₃
            n n' (by omega) ≫
      HomologicalComplex.homologyMap S.g n' := by
  let eG : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj
        (CochainComplex.mappingCone g) ≅ (CochainComplex.mappingCone g).homology n :=
    (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).app
      (CochainComplex.mappingCone g)
  let eS : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n').obj
        (CochainComplex.mappingCone S.f) ≅ (CochainComplex.mappingCone S.f).homology n' :=
    (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n').app
      (CochainComplex.mappingCone S.f)
  let δh : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj
        (CochainComplex.mappingCone g) ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n').obj
          (CochainComplex.mappingCone S.f) :=
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
      (CochainComplex.mappingConeCompTriangleh S.f g) n n' h
  let δ : (CochainComplex.mappingCone g).homology n ⟶ S.X₂.homology n' :=
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (CochainComplex.mappingCone.triangle g).mor₃ n n' (by omega)
  let desc : (CochainComplex.mappingCone S.f).homology n' ⟶ S.X₃.homology n' :=
    HomologicalComplex.homologyMap (CochainComplex.mappingCone.descShortComplex S) n'
  let hg : S.X₂.homology n' ⟶ S.X₃.homology n' :=
    HomologicalComplex.homologyMap S.g n'
  have h₀ : δh ≫ eS.hom ≫ desc = eG.hom ≫ δ ≫ hg :=
    CochainComplex.mappingCone.homologySequenceδ_mappingConeCompTriangleh_comp_descShortComplex
      S g n n' h
  change eG.inv ≫ δh ≫ eS.hom ≫ desc = δ ≫ hg
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun k => eG.inv ≫ k) h₀

private theorem partialTotalConeSpectralConjugation
    {S₀ S₁ K₀ K₁ K₂ L₀ L₁ L₂ : CochainComplex C ℤ}
    (s : S₀ ⟶ S₁) (f₀ : K₀ ⟶ K₁) (g₀ : K₁ ⟶ K₂)
    (f₁ : L₀ ⟶ L₁) (g₁ : L₁ ⟶ L₂)
    (u : ComposableArrows.mk₁ s ⟶ ComposableArrows.mk₁ g₀)
    (v : ComposableArrows.mk₁ f₀ ⟶ ComposableArrows.mk₁ f₁)
    (w : ComposableArrows.mk₁ s ⟶ ComposableArrows.mk₁ g₁)
    (n n' : ℤ) (hnn' : n + 1 = n')
    (h : let Y :=
          (HomotopyCategory.spectralObjectMappingCone C).mapHomologicalFunctor
            (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0);
        (Y.H n).map u ≫ Y.δ f₀ g₀ n n' hnn' ≫ (Y.H n').map v =
          (Y.H n).map w ≫ Y.δ f₁ g₁ n n' hnn') :
    HomologicalComplex.homologyMap
        ((HomotopyCategory.composableArrowsFunctor C).map u) n ≫
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.app
        (CochainComplex.mappingCone g₀) ≫
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingConeCompTriangleh f₀ g₀) n n' hnn' ≫
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n').hom.app
        (CochainComplex.mappingCone f₀) ≫
      HomologicalComplex.homologyMap
        ((HomotopyCategory.composableArrowsFunctor C).map v) n' =
    HomologicalComplex.homologyMap
        ((HomotopyCategory.composableArrowsFunctor C).map w) n ≫
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.app
        (CochainComplex.mappingCone g₁) ≫
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingConeCompTriangleh f₁ g₁) n n' hnn' ≫
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n').hom.app
        (CochainComplex.mappingCone f₁) := by
  let Y :=
    (HomotopyCategory.spectralObjectMappingCone C).mapHomologicalFunctor
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)
  let G := HomotopyCategory.composableArrowsFunctor C
  let invS := (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.app
    (CochainComplex.mappingCone s)
  let facT := (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n').hom.app
    (CochainComplex.mappingCone f₁)
  have hSource : invS ≫ (Y.H n).map u =
      HomologicalComplex.homologyMap (G.map u) n ≫
        (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.app
          (CochainComplex.mappingCone g₀) := by
    rw [partialTotalConeSpectralHMap]
    exact partialTotalHomologyFactors_inv_naturality (G.map u) n
  have hTarget : (Y.H n').map v ≫ facT =
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n').hom.app
          (CochainComplex.mappingCone f₀) ≫
        HomologicalComplex.homologyMap (G.map v) n' := by
    rw [partialTotalConeSpectralHMap]
    exact partialTotalHomologyFactors_hom_naturality (G.map v) n'
  have hCone : invS ≫ (Y.H n).map w =
      HomologicalComplex.homologyMap (G.map w) n ≫
        (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.app
          (CochainComplex.mappingCone g₁) := by
    rw [partialTotalConeSpectralHMap]
    exact partialTotalHomologyFactors_inv_naturality (G.map w) n
  have h' := partialTotalPrePostNaturality invS facT hSource hTarget hCone h
  dsimp only [Y] at h'
  change
    HomologicalComplex.homologyMap (G.map u) n ≫
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.app
        (CochainComplex.mappingCone g₀) ≫
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingConeCompTriangleh f₀ g₀) n n' hnn' ≫
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n').hom.app
        (CochainComplex.mappingCone f₀) ≫
      HomologicalComplex.homologyMap (G.map v) n' =
    HomologicalComplex.homologyMap (G.map w) n ≫
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.app
        (CochainComplex.mappingCone g₁) ≫
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingConeCompTriangleh f₁ g₁) n n' hnn' ≫
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n').hom.app
        (CochainComplex.mappingCone f₁) at h'
  exact h'

private theorem partialTotalConePrecompHMap
    {I : Type*} [Category I] (F : I ⥤ CochainComplex C ℤ)
    {i j : I} (f : i ⟶ j) {D : ComposableArrows I 1}
    (φ : ComposableArrows.mk₁ f ⟶ D) (n : ℤ) :
    let Y := (HomotopyCategory.spectralObjectMappingCone C).mapHomologicalFunctor
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)
    ((((HomotopyCategory.spectralObjectMappingCone C).precomp F).mapHomologicalFunctor
        (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)).H n).map φ =
      (Y.H n).map (F.mapComposableArrowsObjMk₁Iso f).inv ≫
        (Y.H n).map ((F.mapComposableArrows 1).map φ) := by
  let Y := (HomotopyCategory.spectralObjectMappingCone C).mapHomologicalFunctor
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)
  have hInv : (Y.H n).map (F.mapComposableArrowsObjMk₁Iso f).inv = 𝟙 _ := by
    have hCone :
        (HomotopyCategory.composableArrowsFunctor C).map
            (F.mapComposableArrowsObjMk₁Iso f).inv =
          𝟙 (CochainComplex.mappingCone (F.map f)) := by
      dsimp only [CategoryTheory.Functor.mapComposableArrowsObjMk₁Iso,
        HomotopyCategory.composableArrowsFunctor]
      convert CochainComplex.mappingCone.map_id (F.map f) using 1 <;> rfl
    rw [partialTotalConeSpectralHMap, hCone]
    exact (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map_id _
  calc
    _ = (Y.H n).map ((F.mapComposableArrows 1).map φ) := rfl
    _ = _ := partialTotalLeftIdentityEq _ _ hInv

private theorem partialTotalE₁_delta_conjugation (m q : ℕ) :
    let T := B.partialTotalStepCochainShortComplex m
    let S := B.partialTotalStepCochainShortComplex (m + 1)
    let g := B.partialTotalE₁AdjacentCochainMap m q
    let n : ℤ := (core).deg (m + 1, q)
    let n' : ℤ := (core).deg (m, q)
    let hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
      change ((m : ℤ) : EInt) =
        ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
      congr 1
      omega
    let γIdx :
        ComposableArrows.mk₁
            (homOfLE (show (core).i₂ (m, q) ≤ (core).i₂ (m + 1, q) by
              change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
              simp)) ≅
          ComposableArrows.mk₁
            (homOfLE ((core).le₁₂ (m + 1, q))) :=
      ComposableArrows.isoMk₁ (eqToIso hmid) (Iso.refl _)
    let eArrow : ComposableArrows.mk₁ S.f ≅ ComposableArrows.mk₁ g :=
      ComposableArrows.isoMk₁
        (B.partialTotalAdjacentStepCochainIso m) (Iso.refl _) (by
          have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
          change g =
            (B.partialTotalAdjacentStepCochainIso m).inv ≫ S.f at hg
          change S.f ≫ 𝟙 _ =
            (B.partialTotalAdjacentStepCochainIso m).hom ≫ g
          rw [Category.comp_id, hg, Iso.hom_inv_id_assoc])
    let coneMap :=
      (HomotopyCategory.composableArrowsFunctor C).map eArrow.hom
    (B.partialTotalSpectralObjectHStepIso (m + 1) q).inv ≫
        (B.partialTotalSpectralObject.H n).map γIdx.inv ≫
        B.partialTotalSpectralObject.δ
          (homOfLE ((core).le₁₂ (m, q)))
          (homOfLE (show (core).i₂ (m, q) ≤ (core).i₂ (m + 1, q) by
            change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
            simp)) n n' (by
              dsimp only [n, n',
                CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
              omega) ≫
        (B.partialTotalSpectralObjectHStepIso m q).hom =
      HomologicalComplex.homologyMap coneMap n ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone g) ≫
        (HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) 0).homologySequenceδ
            (CochainComplex.mappingConeCompTriangleh T.f g)
              n n' (by
                dsimp only [n, n',
                  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
                omega) ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n').hom.app
            (CochainComplex.mappingCone T.f) := by
  dsimp only
  let T : ShortComplex (CochainComplex C ℤ) := B.partialTotalStepCochainShortComplex m
  let S : ShortComplex (CochainComplex C ℤ) :=
    B.partialTotalStepCochainShortComplex (m + 1)
  let g : T.X₂ ⟶ S.X₂ := B.partialTotalE₁AdjacentCochainMap m q
  let n : ℤ := (core).deg (m + 1, q)
  let n' : ℤ := (core).deg (m, q)
  have hnn' : n + 1 = n' := by
    dsimp only [n, n',
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
    omega
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  let γIdx :
      ComposableArrows.mk₁
          (homOfLE (show (core).i₂ (m, q) ≤ (core).i₂ (m + 1, q) by
            change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
            simp)) ≅
        ComposableArrows.mk₁ (homOfLE ((core).le₁₂ (m + 1, q))) :=
    ComposableArrows.isoMk₁ (eqToIso hmid) (Iso.refl _)
  let D₀ : ComposableArrows (CochainComplex C ℤ) 2 :=
    B.partialTotalE₁AdjacentCoreDiagram m q
  let D₁ : ComposableArrows (CochainComplex C ℤ) 2 :=
    B.partialTotalE₁AdjacentStepDiagram m q
  let d₀₀₁ : B.partialTotalCochainFiltration.obj ((core).i₁ (m, q)) ⟶
      B.partialTotalCochainFiltration.obj ((core).i₂ (m, q)) :=
    D₀.map' 0 1 (by omega) (by omega)
  let d₀₁₂ : B.partialTotalCochainFiltration.obj ((core).i₂ (m, q)) ⟶
      B.partialTotalCochainFiltration.obj ((core).i₂ (m + 1, q)) :=
    D₀.map' 1 2 (by omega) (by omega)
  let d₁₀₁ : T.X₁ ⟶ T.X₂ := D₁.map' 0 1 (by omega) (by omega)
  let d₁₁₂ : T.X₂ ⟶ S.X₂ := D₁.map' 1 2 (by omega) (by omega)
  let E : D₀ ≅ D₁ := B.partialTotalE₁AdjacentDiagramIso m q
  let α : ComposableArrows.mk₁ d₀₀₁ ⟶ ComposableArrows.mk₁ d₁₀₁ :=
    (ComposableArrows.functorArrows (CochainComplex C ℤ) 0 1 2).map E.hom
  let β : ComposableArrows.mk₁ d₀₁₂ ⟶ ComposableArrows.mk₁ d₁₁₂ :=
    (ComposableArrows.functorArrows (CochainComplex C ℤ) 1 2 2).map E.hom
  let Y : CategoryTheory.Abelian.SpectralObject C (CochainComplex C ℤ) :=
    (HomotopyCategory.spectralObjectMappingCone C).mapHomologicalFunctor
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)
  let e₀ := B.partialTotalE₁CochainStepIso m q
  let e₁ := B.partialTotalE₁CochainStepIso (m + 1) q
  let t : B.partialTotalCochainFiltration.obj ((core).i₂ (m, q)) ≅
      B.partialTotalCochainFiltration.obj ((core).i₁ (m + 1, q)) :=
    B.partialTotalE₁MiddleTransportIso m q
  let eA : S.X₁ ≅ T.X₂ := B.partialTotalAdjacentStepCochainIso m
  let eArrow : ComposableArrows.mk₁ S.f ≅ ComposableArrows.mk₁ g :=
    ComposableArrows.isoMk₁ eA (Iso.refl _) (by
      have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
      change g = eA.inv ≫ S.f at hg
      change S.f ≫ 𝟙 _ = eA.hom ≫ g
      rw [Category.comp_id, hg, Iso.hom_inv_id_assoc])
  let coneMap : CochainComplex.mappingCone S.f ⟶
      CochainComplex.mappingCone g :=
    (HomotopyCategory.composableArrowsFunctor C).map eArrow.hom
  have hα : α = e₀.hom := by
    apply ComposableArrows.hom_ext₁
    · rfl
    · rfl
  let γ :
      (ComposableArrows.functorArrows
          (CochainComplex C ℤ) 1 2 2).obj D₀ ≅
        ComposableArrows.mk₁
          (B.partialTotalCochainFiltration.map
            (homOfLE ((core).le₁₂ (m + 1, q)))) :=
    ComposableArrows.isoMk₁ t (Iso.refl _) (by
      have hcore := B.partialTotalE₁CoreSuccessorMap_eq m q
      change d₀₁₂ ≫ 𝟙 _ =
        t.hom ≫ B.partialTotalCochainFiltration.map
          (homOfLE ((core).le₁₂ (m + 1, q)))
      rw [Category.comp_id]
      exact hcore)
  let eSource : ComposableArrows.mk₁ d₀₁₂ ≅ ComposableArrows.mk₁ S.f := γ ≪≫ e₁
  let eRight : ComposableArrows.mk₁ d₀₁₂ ≅ ComposableArrows.mk₁ d₁₁₂ :=
    (ComposableArrows.functorArrows (CochainComplex C ℤ) 1 2 2).mapIso E
  have hSourceβ : eSource.symm ≪≫ eRight = eArrow := by
    apply Iso.ext
    apply ComposableArrows.hom_ext₁
    · change ComposableArrows.app' eSource.inv 0 ≫
        ComposableArrows.app' eRight.hom 0 =
          ComposableArrows.app' eArrow.hom 0
      have hs : ComposableArrows.app' eSource.inv 0 =
          (e₁.app 0).inv ≫ t.inv := rfl
      have hr : ComposableArrows.app' eRight.hom 0 =
          (e₀.app 1).hom := by
        dsimp only [eRight, E]
        rfl
      have ha : ComposableArrows.app' eArrow.hom 0 = eA.hom := rfl
      rw [hs, hr, ha]
      have hm := congrArg Iso.inv (B.partialTotalE₁_middle_iso m q)
      dsimp only [e₀, e₁, t, eA] at hm ⊢
      simpa only [Iso.trans_inv, Iso.symm_inv,
        Category.assoc] using hm
    · change ComposableArrows.app' eSource.inv 1 ≫
        ComposableArrows.app' eRight.hom 1 =
          ComposableArrows.app' eArrow.hom 1
      have hs : ComposableArrows.app' eSource.inv 1 =
          (e₁.app 1).inv := by
        dsimp only [eSource, γ, Iso.trans_inv]
        change (e₁.app 1).inv ≫ 𝟙 _ = (e₁.app 1).inv
        simp only [Category.comp_id]
      have hr : ComposableArrows.app' eRight.hom 1 =
          (e₁.app 1).hom := by
        dsimp only [eRight, E]
        rfl
      have ha : ComposableArrows.app' eArrow.hom 1 = 𝟙 _ := rfl
      rw [hs, hr, ha, Iso.inv_hom_id]
  let sourceMap : CochainComplex.mappingCone S.f ⟶
      CochainComplex.mappingCone d₀₁₂ :=
    (HomotopyCategory.composableArrowsFunctor C).map eSource.inv
  let targetMap : CochainComplex.mappingCone d₀₀₁ ⟶
      CochainComplex.mappingCone T.f :=
    (HomotopyCategory.composableArrowsFunctor C).map α
  have hHomotopy :
      (Y.H n).map eSource.inv ≫
          Y.δ d₀₀₁ d₀₁₂ n n' hnn' ≫
          (Y.H n').map α =
        (Y.H n).map eArrow.hom ≫
          Y.δ d₁₀₁ d₁₁₂ n n' hnn' := by
    have hSource : eArrow.hom = eSource.inv ≫ β := by
      have h := congrArg Iso.hom hSourceβ
      change eSource.inv ≫ β = eArrow.hom at h
      exact h.symm
    exact partialTotalSpectralδ_precompose Y d₀₀₁ d₀₁₂ d₁₀₁ d₁₁₂
      α β eSource.inv eArrow.hom hSource n n' (by rfl) hnn'
  let F₀ : HomotopyCategory C (ComplexShape.up ℤ) ⥤ C :=
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0
  have hSourceMap :
      (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone S.f) ≫
        (Y.H n).map eSource.inv =
      HomologicalComplex.homologyMap sourceMap n ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone d₀₁₂) := by
    rw [partialTotalConeSpectralHMap]
    exact partialTotalHomologyFactors_inv_naturality sourceMap n
  have hHomotopy' := partialTotalConeSpectralConjugation
    S.f d₀₀₁ d₀₁₂ T.f g eSource.inv α eArrow.hom n n' hnn' hHomotopy
  let F : EInt ⥤ CochainComplex C ℤ := B.partialTotalCochainFiltration
  let fIdx : (core).i₁ (m, q) ⟶ (core).i₂ (m, q) :=
    homOfLE ((core).le₁₂ (m, q))
  let gIdx : (core).i₂ (m, q) ⟶ (core).i₂ (m + 1, q) :=
    homOfLE (show (core).i₂ (m, q) ≤
      (core).i₂ (m + 1, q) by
    change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
    simp)
  let eF := F.mapComposableArrowsObjMk₁Iso fIdx
  let eG := F.mapComposableArrowsObjMk₁Iso gIdx
  have hdF : F.map fIdx = d₀₀₁ := by
    dsimp only [F, fIdx, d₀₀₁, D₀,
      partialTotalE₁AdjacentCoreDiagram]
    convert rfl using 1
    subsingleton
  have hdG : F.map gIdx = d₀₁₂ := by
    dsimp only [F, gIdx, d₀₁₂, D₀,
      partialTotalE₁AdjacentCoreDiagram]
    convert rfl using 1
    subsingleton
  let iF : ComposableArrows.mk₁ (F.map fIdx) ≅
      ComposableArrows.mk₁ d₀₀₁ :=
    ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _) (by
      change F.map fIdx ≫ 𝟙 _ = 𝟙 _ ≫ d₀₀₁
      simpa only [Category.comp_id, Category.id_comp] using hdF)
  let iG : ComposableArrows.mk₁ (F.map gIdx) ≅
      ComposableArrows.mk₁ d₀₁₂ :=
    ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _) (by
      change F.map gIdx ≫ 𝟙 _ = 𝟙 _ ≫ d₀₁₂
      simpa only [Category.comp_id, Category.id_comp] using hdG)
  have hiFInv : iF.inv = 𝟙 _ := by
    apply ComposableArrows.hom_ext₁ <;> rfl
  have hiGHom : iG.hom = 𝟙 _ := by
    apply ComposableArrows.hom_ext₁ <;> rfl
  let eFCore := eF ≪≫ iF
  let eGCore := eG ≪≫ iG
  let canonicalMap : F.obj ((core).i₁ (m + 1, q)) ⟶
      F.obj ((core).i₂ (m + 1, q)) := F.map (homOfLE ((core).le₁₂ (m + 1, q)))
  let eC := F.mapComposableArrowsObjMk₁Iso
    (homOfLE ((core).le₁₂ (m + 1, q)))
  have hSourceArrowF :
      e₁.inv ≫ eC.inv ≫
          (F.mapComposableArrows 1).map γIdx.inv ≫ eG.hom =
        eSource.inv := by
    have ht : F.map (eqToHom hmid.symm) = t.inv := by
      dsimp only [t, partialTotalE₁MiddleTransportIso]
      convert CategoryTheory.eqToHom_map F hmid.symm using 1
      subsingleton
    have he10 : ComposableArrows.app' e₁.inv 0 = (e₁.app 0).inv := rfl
    have he11 : ComposableArrows.app' e₁.inv 1 = (e₁.app 1).inv := rfl
    have heC0 : ComposableArrows.app' eC.inv 0 = 𝟙 _ := rfl
    have heC1 : ComposableArrows.app' eC.inv 1 = 𝟙 _ := rfl
    have hγ0 : ComposableArrows.app'
        ((F.mapComposableArrows 1).map γIdx.inv) 0 =
        F.map (eqToHom hmid.symm) := by
      convert rfl using 1
      subsingleton
    have hγ1 : ComposableArrows.app'
        ((F.mapComposableArrows 1).map γIdx.inv) 1 = 𝟙 _ := by
      change F.map (𝟙 _) = 𝟙 _
      exact F.map_id _
    have heG0 : ComposableArrows.app' eG.hom 0 = 𝟙 _ := rfl
    have heG1 : ComposableArrows.app' eG.hom 1 = 𝟙 _ := rfl
    have hsrc0 : ComposableArrows.app' eSource.inv 0 =
        (e₁.app 0).inv ≫ t.inv := rfl
    have hsrc1 : ComposableArrows.app' eSource.inv 1 =
        (e₁.app 1).inv ≫ 𝟙 _ := rfl
    apply ComposableArrows.hom_ext₁
    · simp only [NatTrans.comp_app, he10, heC0, hγ0, heG0, hsrc0]
      rw [ht]
      cat_disch
    · simp only [NatTrans.comp_app, he11, heC1, hγ1,
        heG1, hsrc1]
      cat_disch
  have hPrecompGamma :
      (B.partialTotalSpectralObject.H n).map γIdx.inv =
        (Y.H n).map eC.inv ≫
          (Y.H n).map ((F.mapComposableArrows 1).map γIdx.inv) :=
    partialTotalConePrecompHMap F (homOfLE ((core).le₁₂ (m + 1, q))) γIdx.inv n
  have hSourceFunctor := congrArg (Y.H n).map hSourceArrowF
  simp only [Functor.map_comp] at hSourceFunctor
  have hTargetArrowF : eF.inv ≫ eF.hom ≫ e₀.hom = α := by
    rw [Iso.inv_hom_id_assoc]
    rw [hα]
  have hTargetArrow :
      iF.inv ≫ eF.inv ≫ eF.hom ≫ e₀.hom = α := by
    rw [hiFInv]
    exact (Category.id_comp (eF.inv ≫ eF.hom ≫ e₀.hom)).trans hTargetArrowF
  let stepInvMap : CochainComplex.mappingCone S.f ⟶
      CochainComplex.mappingCone canonicalMap :=
    (HomotopyCategory.composableArrowsFunctor C).map e₁.inv
  have hStepNatural :
      HomologicalComplex.homologyMap stepInvMap n ≫
          (HomotopyCategory.homologyFunctorFactors C
            (ComplexShape.up ℤ) n).inv.app
              (CochainComplex.mappingCone canonicalMap) =
        (HomotopyCategory.homologyFunctorFactors C
            (ComplexShape.up ℤ) n).inv.app
              (CochainComplex.mappingCone S.f) ≫
          (Y.H n).map e₁.inv := by
    rw [partialTotalConeSpectralHMap]
    exact (partialTotalHomologyFactors_inv_naturality stepInvMap n).symm
  have hSourceCoordinate :
      (B.partialTotalSpectralObjectHStepIso (m + 1) q).inv ≫
          (B.partialTotalSpectralObject.H n).map γIdx.inv ≫
          (Y.H n).map eGCore.hom =
        HomologicalComplex.homologyMap sourceMap n ≫
          (HomotopyCategory.homologyFunctorFactors
            C (ComplexShape.up ℤ) n).inv.app
              (CochainComplex.mappingCone d₀₁₂) := by
    have hStepInvCoordinate :
        (B.partialTotalSpectralObjectHStepIso (m + 1) q).inv =
          HomologicalComplex.homologyMap stepInvMap n ≫
            (HomotopyCategory.homologyFunctorFactors C
              (ComplexShape.up ℤ) n).inv.app
                (CochainComplex.mappingCone canonicalMap) := rfl
    have hCoreG : (Y.H n).map eGCore.hom = (Y.H n).map eG.hom := by
      have hArrow : eGCore.hom = eG.hom := by
        dsimp only [eGCore, Iso.trans_hom]
        erw [hiGHom]
        exact Category.comp_id _
      exact (Y.H n).congr_map hArrow
    exact partialTotalSourceCoordinateEq hStepInvCoordinate hPrecompGamma hCoreG
      hStepNatural hSourceFunctor hSourceMap
  have hConeFHom :
      (HomotopyCategory.composableArrowsFunctor C).map eF.hom =
        𝟙 (CochainComplex.mappingCone (F.map fIdx)) := by
    dsimp only [eF,
      CategoryTheory.Functor.mapComposableArrowsObjMk₁Iso,
      HomotopyCategory.composableArrowsFunctor]
    convert CochainComplex.mappingCone.map_id (F.map fIdx) using 1 <;> rfl
  let targetBridgeMap : CochainComplex.mappingCone d₀₀₁ ⟶
      CochainComplex.mappingCone (F.map fIdx) :=
    (HomotopyCategory.composableArrowsFunctor C).map
      (eFCore.inv ≫ eF.hom)
  have hTargetBridgeMap_eq :
      targetBridgeMap =
        (HomotopyCategory.composableArrowsFunctor C).map eFCore.inv := by
    dsimp only [targetBridgeMap]
    rw [(HomotopyCategory.composableArrowsFunctor C).map_comp,
      hConeFHom]
    exact Category.comp_id _
  have hTargetBridgeMap :
      (Y.H n').map eFCore.inv =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
          HomotopyCategory.homologyFunctor C
            (ComplexShape.up ℤ) n').map targetBridgeMap := by
    change (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n').map
          ((HomotopyCategory.composableArrowsFunctor C).map eFCore.inv) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n').map targetBridgeMap
    exact (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n').congr_map
        hTargetBridgeMap_eq.symm
  have hTargetNatural :
      (Y.H n').map eFCore.inv ≫
          (HomotopyCategory.homologyFunctorFactors C
            (ComplexShape.up ℤ) n').hom.app
              (CochainComplex.mappingCone (F.map fIdx)) =
        (HomotopyCategory.homologyFunctorFactors C
            (ComplexShape.up ℤ) n').hom.app
              (CochainComplex.mappingCone d₀₀₁) ≫
          HomologicalComplex.homologyMap targetBridgeMap n' := by
    rw [hTargetBridgeMap]
    exact partialTotalHomologyFactors_hom_naturality targetBridgeMap n'
  let stepHomMap : CochainComplex.mappingCone (F.map fIdx) ⟶
      CochainComplex.mappingCone T.f :=
    (HomotopyCategory.composableArrowsFunctor C).map e₀.hom
  have hTargetBridgeComposite :
      targetBridgeMap ≫ stepHomMap = targetMap := by
    dsimp only [targetBridgeMap, targetMap, stepHomMap]
    calc
      _ = (HomotopyCategory.composableArrowsFunctor C).map
          ((eFCore.inv ≫ eF.hom) ≫ e₀.hom) :=
        ((HomotopyCategory.composableArrowsFunctor C).map_comp
          (eFCore.inv ≫ eF.hom) e₀.hom).symm
      _ = _ := (HomotopyCategory.composableArrowsFunctor C).congr_map (by
        simpa only [eFCore, Iso.trans_inv, Category.assoc] using hTargetArrow)
  have hTargetCoordinate :
      (Y.H n').map eFCore.inv ≫
          (B.partialTotalSpectralObjectHStepIso m q).hom =
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n').hom.app
            (CochainComplex.mappingCone d₀₀₁) ≫
          HomologicalComplex.homologyMap targetMap n' := by
    have hStepHomCoordinate :
        (B.partialTotalSpectralObjectHStepIso m q).hom =
          (HomotopyCategory.homologyFunctorFactors C
            (ComplexShape.up ℤ) n').hom.app
              (CochainComplex.mappingCone (F.map fIdx)) ≫
            HomologicalComplex.homologyMap stepHomMap n' := rfl
    have hComp := HomologicalComplex.homologyMap_comp targetBridgeMap stepHomMap n'
    have hTarget := congrArg
      (fun t : CochainComplex.mappingCone d₀₀₁ ⟶ CochainComplex.mappingCone T.f =>
        HomologicalComplex.homologyMap t n') hTargetBridgeComposite
    exact partialTotalTargetCoordinateEq hStepHomCoordinate hTargetNatural
      (hComp.symm.trans hTarget)
  have hDeltaF :
      B.partialTotalSpectralObject.δ fIdx gIdx n n' hnn' =
        (Y.H n).map eG.hom ≫
          Y.δ (F.map fIdx) (F.map gIdx) n n' hnn' ≫
        (Y.H n').map eF.inv := by
    dsimp only [partialTotalSpectralObject]
    rw [CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor_δ
      (X := B.partialTotalHomotopySpectralObject) F₀ fIdx gIdx n n' hnn']
    dsimp only [partialTotalHomotopySpectralObject,
      CategoryTheory.Triangulated.SpectralObject.triangle,
      CategoryTheory.Triangulated.SpectralObject.precomp,
      CategoryTheory.Triangulated.SpectralObject.δ,
      CategoryTheory.Functor.homologySequenceδ]
    simp only [Pretriangulated.Triangle.mk_mor₃]
    rw [F₀.shiftMap_comp', F₀.shiftMap_comp]
    rfl
  have hδCoreNat := Y.δ_naturality
    (F.map fIdx) (F.map gIdx) d₀₀₁ d₀₁₂
    iF.hom iG.hom n n' (by rfl) hnn'
  have hδCore :
      Y.δ (F.map fIdx) (F.map gIdx) n n' hnn' =
        (Y.H n).map iG.hom ≫
          Y.δ d₀₀₁ d₀₁₂ n n' hnn' ≫
        (Y.H n').map iF.inv := by
    symm
    rw [← Category.assoc, hδCoreNat, Category.assoc,
      ← (Y.H n').map_comp, Iso.hom_inv_id, (Y.H n').map_id,
      Category.comp_id]
  have hDelta :
      B.partialTotalSpectralObject.δ fIdx gIdx n n' hnn' =
        (Y.H n).map eGCore.hom ≫
          Y.δ d₀₀₁ d₀₁₂ n n' hnn' ≫
        (Y.H n').map eFCore.inv := by
    rw [hDeltaF, hδCore]
    dsimp only [eGCore, eFCore, Iso.trans_hom, Iso.trans_inv]
    rw [(Y.H n).map_comp, (Y.H n').map_comp]
    simp only [Category.assoc]
    rfl
  have hRawDelta :
      Y.δ d₀₀₁ d₀₁₂ n n' hnn' =
        F₀.homologySequenceδ
          (CochainComplex.mappingConeCompTriangleh
            d₀₀₁ d₀₁₂)
            n n' hnn' := by
    rfl
  exact partialTotalConjugateCoordinatesEq hDelta hSourceCoordinate hTargetCoordinate
    hRawDelta hHomotopy'

private theorem partialTotalE₁_mappingConeDifferential_eq_connecting
    (m q : ℕ)
    (hnn' : (core).deg (m + 1, q) + 1 = (core).deg (m, q)) :
    let T := B.partialTotalStepCochainShortComplex m
    let S := B.partialTotalStepCochainShortComplex (m + 1)
    let g := B.partialTotalE₁AdjacentCochainMap m q
    let n : ℤ := (core).deg (m + 1, q)
    let n' : ℤ := (core).deg (m, q)
    let eArrow : ComposableArrows.mk₁ S.f ≅ ComposableArrows.mk₁ g :=
      ComposableArrows.isoMk₁
        (B.partialTotalAdjacentStepCochainIso m) (Iso.refl _) (by
          have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
          change g =
            (B.partialTotalAdjacentStepCochainIso m).inv ≫ S.f at hg
          change S.f ≫ 𝟙 _ =
            (B.partialTotalAdjacentStepCochainIso m).hom ≫ g
          rw [Category.comp_id, hg, Iso.hom_inv_id_assoc])
    let coneMap :=
      (HomotopyCategory.composableArrowsFunctor C).map eArrow.hom
    (B.partialTotalStepE₁HomologyIso (m + 1) q).inv ≫
        HomologicalComplex.homologyMap coneMap n ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone g) ≫
        (HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) 0).homologySequenceδ
            (CochainComplex.mappingConeCompTriangleh T.f g) n n' hnn' ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n').hom.app
            (CochainComplex.mappingCone T.f) ≫
        (B.partialTotalStepE₁HomologyIso m q).hom =
      B.partialTotalE₁ConnectingDifferential m q := by
  dsimp only
  let T : ShortComplex (CochainComplex C ℤ) := B.partialTotalStepCochainShortComplex m
  let S : ShortComplex (CochainComplex C ℤ) :=
    B.partialTotalStepCochainShortComplex (m + 1)
  let eA : S.X₁ ≅ T.X₂ := B.partialTotalAdjacentStepCochainIso m
  let g : T.X₂ ⟶ S.X₂ := B.partialTotalE₁AdjacentCochainMap m q
  let hS : S.ShortExact :=
    B.partialTotalStepCochainShortExact (m + 1)
  let hT : T.ShortExact := B.partialTotalStepCochainShortExact m
  let R : ShortComplex (CochainComplex C ℤ) :=
    ShortComplex.mk g S.g (by
      dsimp only [g]
      rw [B.partialTotalE₁AdjacentCochainMap_eq m q,
        Category.assoc, S.zero, comp_zero])
  let eS : S ≅ R :=
    ShortComplex.isoMk eA (Iso.refl _) (Iso.refl _)
      (by
        dsimp only [R]
        have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
        change g = eA.inv ≫ S.f at hg
        change eA.hom ≫ g = S.f ≫ 𝟙 _
        rw [hg, Iso.hom_inv_id_assoc, Category.comp_id])
      (by
        dsimp only [R]
        change (𝟙 S.X₂) ≫ S.g = S.g ≫ 𝟙 S.X₃
        simp only [Category.id_comp, Category.comp_id])
  let hR : R.ShortExact := ShortComplex.shortExact_of_iso eS hS
  let eArrow : ComposableArrows.mk₁ S.f ≅ ComposableArrows.mk₁ g :=
    ComposableArrows.isoMk₁
      (B.partialTotalAdjacentStepCochainIso m) (Iso.refl _) (by
        have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
        change g =
          (B.partialTotalAdjacentStepCochainIso m).inv ≫ S.f at hg
        change S.f ≫ 𝟙 _ =
          (B.partialTotalAdjacentStepCochainIso m).hom ≫ g
        rw [Category.comp_id, hg, Iso.hom_inv_id_assoc])
  let coneMap : CochainComplex.mappingCone S.f ⟶
      CochainComplex.mappingCone g :=
    (HomotopyCategory.composableArrowsFunctor C).map eArrow.hom
  let descS : CochainComplex.mappingCone S.f ⟶ S.X₃ :=
    CochainComplex.mappingCone.descShortComplex S
  let descR : CochainComplex.mappingCone R.f ⟶ R.X₃ :=
    CochainComplex.mappingCone.descShortComplex R
  let descT : CochainComplex.mappingCone T.f ⟶ T.X₃ :=
    CochainComplex.mappingCone.descShortComplex T
  let _ : QuasiIso descS :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS
  let _ : QuasiIso descR :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hR
  let _ : QuasiIso descT :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hT
  let n : ℤ := (core).deg (m + 1, q)
  let n' : ℤ := (core).deg (m, q)
  have hDescChain : coneMap ≫ descR = descS := by
    have h := CochainComplex.mappingCone.descShortComplex_naturality eS.hom
    change coneMap ≫ descR = descS ≫ eS.hom.τ₃ at h
    have hτ₃ : eS.hom.τ₃ = 𝟙 _ := rfl
    rw [hτ₃, Category.comp_id] at h
    exact h
  have hDesc :
      HomologicalComplex.homologyMap coneMap n ≫
          HomologicalComplex.homologyMap descR n =
        HomologicalComplex.homologyMap descS n := by
    rw [← HomologicalComplex.homologyMap_comp, hDescChain]
  have hδShort :
      hS.δ n n' hnn' ≫ HomologicalComplex.homologyMap eA.hom n' =
        hR.δ n n' hnn' := by
    have h := HomologicalComplex.HomologySequence.δ_naturality
      eS.hom hS hR n n' hnn'
    have hτ₁ : eS.hom.τ₁ = eA.hom := rfl
    have hτ₃ : eS.hom.τ₃ = 𝟙 _ := rfl
    rw [hτ₁, hτ₃, HomologicalComplex.homologyMap_id,
      Category.id_comp] at h
    exact h
  let ePlus : (CochainComplex.mappingCone S.f).homology n ≅
      (B.totalRow (m + 1)).homology (m + 1 + q) :=
    B.partialTotalStepE₁HomologyIso (m + 1) q
  let eZero : (CochainComplex.mappingCone T.f).homology n' ≅
      (B.totalRow m).homology (m + q) := B.partialTotalStepE₁HomologyIso m q
  let rPlus : S.X₃.homology n ≅ (B.totalRow (m + 1)).homology (m + 1 + q) :=
    HomologicalComplex.homologyMapIso (B.partialTotalStepCochainX₃Iso (m + 1)) n ≪≫
      (B.totalRow (m + 1)).extendHomologyIso ComplexShape.embeddingDownNat (by
        change -((m + 1 + q : ℕ) : ℤ) = n
        dsimp only [n, CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
        omega)
  let rZero : T.X₃.homology n' ≅ (B.totalRow m).homology (m + q) :=
    HomologicalComplex.homologyMapIso (B.partialTotalStepCochainX₃Iso m) n' ≪≫
      (B.totalRow m).extendHomologyIso ComplexShape.embeddingDownNat (by
        change -((m + q : ℕ) : ℤ) = n'
        dsimp only [n', CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
        omega)
  let hm : (CochainComplex.mappingCone S.f).homology n ⟶
      (CochainComplex.mappingCone g).homology n := HomologicalComplex.homologyMap coneMap n
  let dS : (CochainComplex.mappingCone S.f).homology n ⟶ S.X₃.homology n :=
    HomologicalComplex.homologyMap descS n
  let dR : (CochainComplex.mappingCone g).homology n ⟶ S.X₃.homology n :=
    HomologicalComplex.homologyMap descR n
  let dT : (CochainComplex.mappingCone T.f).homology n' ⟶ T.X₃.homology n' :=
    HomologicalComplex.homologyMap descT n'
  let hg : T.X₂.homology n' ⟶ T.X₃.homology n' := HomologicalComplex.homologyMap T.g n'
  let δR : S.X₃.homology n ⟶ T.X₂.homology n' := hR.δ n n' hnn'
  let shiftδ : (CochainComplex.mappingCone g).homology n ⟶ T.X₂.homology n' :=
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (CochainComplex.mappingCone.triangle g).mor₃ n n' (by omega)
  let z : (CochainComplex.mappingCone g).homology n ⟶
      (CochainComplex.mappingCone T.f).homology n' :=
    (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.app
        (CochainComplex.mappingCone g) ≫
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingConeCompTriangleh T.f g) n n' hnn' ≫
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n').hom.app
        (CochainComplex.mappingCone T.f)
  have heZero : eZero.hom = dT ≫ rZero.hom := rfl
  have hz : z ≫ dT = shiftδ ≫ hg := by
    dsimp only [z, dT, descT, shiftδ, hg]
    exact partialTotalThreePostEq
      (mappingCone_homologySequenceδ_normalized T g n n' hnn')
  have hshift : shiftδ = dR ≫ δR :=
    mappingCone_shiftMap_eq_shortExact R hR n n' hnn'
  have hdesc : hm ≫ dR = dS := hDesc
  have hePlus : ePlus = asIso dS ≪≫ rPlus := rfl
  have hcancel : ePlus.inv ≫ dS = rPlus.inv := by
    rw [hePlus]
    change (rPlus.inv ≫ (asIso dS).inv) ≫ (asIso dS).hom = rPlus.inv
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hCollapse : ePlus.inv ≫ hm ≫ z ≫ eZero.hom =
      rPlus.inv ≫ δR ≫ hg ≫ rZero.hom :=
    partialTotalConeCoordinateCollapse ePlus.inv hm z eZero.hom dT rZero.hom
      shiftδ hg dR δR dS rPlus.inv heZero hz hshift hdesc hcancel
  have hFinal : rPlus.inv ≫ δR ≫ hg ≫ rZero.hom =
      B.partialTotalE₁ConnectingDifferential m q := by
    have hδR : δR = hS.δ n n' hnn' ≫ HomologicalComplex.homologyMap eA.hom n' :=
      hδShort.symm
    rw [hδR]
    have hδS : hS.δ n n' hnn' =
        (B.partialTotalStepCochainShortExact (m + 1)).δ n n' hnn' := rfl
    rw [hδS]
    have hn : ComplexShape.embeddingDownNat.f (m + 1 + q) = n := by
      dsimp only [n,
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
      change -((m + 1 + q : ℕ) : ℤ) =
        -((m + 1 : ℕ) : ℤ) - (q : ℤ)
      omega
    have hn' : ComplexShape.embeddingDownNat.f (m + q) = n' := by
      dsimp only [n',
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
      change -((m + q : ℕ) : ℤ) = -(m : ℤ) - (q : ℤ)
      omega
    have hn₀ : n = -((m + 1 + q : ℕ) : ℤ) := by
      dsimp only [n,
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
      omega
    have hn₀' : n' = -((m + q : ℕ) : ℤ) := by
      dsimp only [n',
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
      omega
    let D := { d : ℤ × ℤ //
      ComplexShape.embeddingDownNat.f (m + 1 + q) = d.1 ∧
        ComplexShape.embeddingDownNat.f (m + q) = d.2 }
    let dCore : D := ⟨(n, n'), hn, hn'⟩
    let dNat : D := ⟨
      (-((m + 1 + q : ℕ) : ℤ), -((m + q : ℕ) : ℤ)), rfl, rfl⟩
    have hRel (d : D) : d.1.1 + 1 = d.1.2 := by
      rw [← d.2.1, ← d.2.2]
      change -((m + 1 + q : ℕ) : ℤ) + 1 =
        -((m + q : ℕ) : ℤ)
      omega
    let wholeAt (d : D) :
        (B.totalRow (m + 1)).homology (m + 1 + q) ⟶
          (B.totalRow m).homology (m + q) :=
      ((B.totalRow (m + 1)).extendHomologyIso
          ComplexShape.embeddingDownNat d.2.1).inv ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalStepCochainX₃Iso (m + 1)) d.1.1).inv ≫
        (B.partialTotalStepCochainShortExact (m + 1)).δ d.1.1 d.1.2 (hRel d) ≫
        (HomologicalComplex.homologyMapIso eA d.1.2).hom ≫
        HomologicalComplex.homologyMap T.g d.1.2 ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalStepCochainX₃Iso m) d.1.2).hom ≫
        ((B.totalRow m).extendHomologyIso
          ComplexShape.embeddingDownNat d.2.2).hom
    have hd : dCore = dNat := by
      apply Subtype.ext
      apply Prod.ext
      · exact hn₀
      · exact hn₀'
    have hleft :
        rPlus.inv ≫
            ((B.partialTotalStepCochainShortExact (m + 1)).δ n n' hnn' ≫
              HomologicalComplex.homologyMap eA.hom n') ≫
            hg ≫ rZero.hom = wholeAt dCore := by
      dsimp only [rPlus, rZero, hg, wholeAt, dCore, D, Iso.trans_inv, Iso.trans_hom,
        HomologicalComplex.homologyMapIso_hom]
      exact partialTotalSevenReassoc _ _ _ _ _ _ _
    have hright : wholeAt dNat = B.partialTotalE₁ConnectingDifferential m q := rfl
    exact hleft.trans ((congrArg wholeAt hd).trans hright)
  exact partialTotalUnfoldMiddleThreeEq (hCollapse.trans hFinal)

private theorem partialTotalE₁_mappingConeDifferential_eq_connectingAt
    (m q nPlus nZero : ℕ)
    (hPlus : (m + 1) + q = nPlus)
    (hZero : m + q = nZero)
    (hSProof :
      (B.partialTotalStepCochainShortComplex (m + 1)).ShortExact)
    (hν : -((nPlus : ℕ) : ℤ) + 1 = -((nZero : ℕ) : ℤ))
    (hnn' : (core).deg (m + 1, q) + 1 = (core).deg (m, q)) :
    let T := B.partialTotalStepCochainShortComplex m
    let S := B.partialTotalStepCochainShortComplex (m + 1)
    let g := B.partialTotalE₁AdjacentCochainMap m q
    let n : ℤ := (core).deg (m + 1, q)
    let n' : ℤ := (core).deg (m, q)
    let eArrow : ComposableArrows.mk₁ S.f ≅ ComposableArrows.mk₁ g :=
      ComposableArrows.isoMk₁
        (B.partialTotalAdjacentStepCochainIso m) (Iso.refl _) (by
          have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
          change g =
            (B.partialTotalAdjacentStepCochainIso m).inv ≫ S.f at hg
          change S.f ≫ 𝟙 _ =
            (B.partialTotalAdjacentStepCochainIso m).hom ≫ g
          rw [Category.comp_id, hg, Iso.hom_inv_id_assoc])
    let coneMap :=
      (HomotopyCategory.composableArrowsFunctor C).map eArrow.hom
    let eNat := ComplexShape.embeddingDownNat
    let νPlus : ℤ := -((nPlus : ℕ) : ℤ)
    let νZero : ℤ := -((nZero : ℕ) : ℤ)
    let hS : S.ShortExact := hSProof
    let cAt :
        (B.totalRow (m + 1)).homology nPlus ⟶
          (B.totalRow m).homology nZero :=
      ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalStepCochainX₃Iso (m + 1)) νPlus).inv ≫
        hS.δ νPlus νZero hν ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalAdjacentStepCochainIso m) νZero).hom ≫
        HomologicalComplex.homologyMap T.g νZero ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalStepCochainX₃Iso m) νZero).hom ≫
        ((B.totalRow m).extendHomologyIso eNat rfl).hom
    (B.partialTotalStepE₁HomologyIsoAt (m + 1) q nPlus hPlus).inv ≫
        (HomologicalComplex.homologyMap coneMap n ≫
          (HomotopyCategory.homologyFunctorFactors
            C (ComplexShape.up ℤ) n).inv.app
              (CochainComplex.mappingCone g) ≫
          (HomotopyCategory.homologyFunctor C
            (ComplexShape.up ℤ) 0).homologySequenceδ
              (CochainComplex.mappingConeCompTriangleh T.f g) n n' hnn' ≫
          (HomotopyCategory.homologyFunctorFactors
            C (ComplexShape.up ℤ) n').hom.app
              (CochainComplex.mappingCone T.f)) ≫
        (B.partialTotalStepE₁HomologyIsoAt m q nZero hZero).hom =
      cAt := by
  subst nPlus
  subst nZero
  have hIsoPlus :
      B.partialTotalStepE₁HomologyIsoAt
          (m + 1) q ((m + 1) + q) rfl =
        B.partialTotalStepE₁HomologyIso (m + 1) q := by
    rfl
  have hIsoZero :
      B.partialTotalStepE₁HomologyIsoAt m q (m + q) rfl =
        B.partialTotalStepE₁HomologyIso m q := by
    rfl
  rw [hIsoPlus, hIsoZero]
  change _ = B.partialTotalE₁ConnectingDifferential m q
  let T := B.partialTotalStepCochainShortComplex m
  let S := B.partialTotalStepCochainShortComplex (m + 1)
  let g := B.partialTotalE₁AdjacentCochainMap m q
  let n : ℤ := (core).deg (m + 1, q)
  let n' : ℤ := (core).deg (m, q)
  let eArrow : ComposableArrows.mk₁ S.f ≅ ComposableArrows.mk₁ g :=
    ComposableArrows.isoMk₁
      (B.partialTotalAdjacentStepCochainIso m) (Iso.refl _) (by
        have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
        change g =
          (B.partialTotalAdjacentStepCochainIso m).inv ≫ S.f at hg
        change S.f ≫ 𝟙 _ =
          (B.partialTotalAdjacentStepCochainIso m).hom ≫ g
        rw [Category.comp_id, hg, Iso.hom_inv_id_assoc])
  let coneMap :=
    (HomotopyCategory.composableArrowsFunctor C).map eArrow.hom
  let HPlus := B.partialTotalStepE₁Homology (m + 1) q
  let HG := HomologicalComplex.homology
    (CochainComplex.mappingCone g) n
  let QG := ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj
      (CochainComplex.mappingCone g))
  let QT := ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n').obj
      (CochainComplex.mappingCone T.f))
  let HZero := B.partialTotalStepE₁Homology m q
  let a := (B.partialTotalStepE₁HomologyIso (m + 1) q).inv
  let b : HPlus ⟶ HG := HomologicalComplex.homologyMap coneMap n
  let c : HG ⟶ QG := (HomotopyCategory.homologyFunctorFactors
    C (ComplexShape.up ℤ) n).inv.app (CochainComplex.mappingCone g)
  let d : QG ⟶ QT := (HomotopyCategory.homologyFunctor C
    (ComplexShape.up ℤ) 0).homologySequenceδ
      (CochainComplex.mappingConeCompTriangleh T.f g) n n' hnn'
  let e : QT ⟶ HZero := (HomotopyCategory.homologyFunctorFactors
    C (ComplexShape.up ℤ) n').hom.app (CochainComplex.mappingCone T.f)
  let f := (B.partialTotalStepE₁HomologyIso m q).hom
  have hAssoc : (b ≫ c ≫ d ≫ e) ≫ f =
      b ≫ c ≫ d ≫ e ≫ f := by
    simp only [Category.assoc]
  have h :=
    B.partialTotalE₁_mappingConeDifferential_eq_connecting m q hnn'
  dsimp only at h
  change a ≫ ((b ≫ c ≫ d ≫ e) ≫ f) =
    B.partialTotalE₁ConnectingDifferential m q
  rw [hAssoc]
  change a ≫ (b ≫ c ≫ d ≫ e ≫ f) =
    B.partialTotalE₁ConnectingDifferential m q at h
  exact h

/-- First-page row differential equals the step connecting morphism.

For natural `m` and `q`, the first-page differential transported from `(m + 1, q)` to `(m, q)`
in total-row homology equals `B.partialTotalE₁ConnectingDifferential m q`. -/
@[reassoc]
theorem partialTotalE₁RowDifferential_eq_connecting (m q : ℕ) :
    B.partialTotalE₁RowDifferential m q =
      B.partialTotalE₁ConnectingDifferential m q := by
  let P₁ : HomologicalComplex C
      (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩) :=
    (B.partialTotalSpectralObject.spectralSequence core).page 1
  let n : ℤ := (core).deg (m + 1, q)
  let n' : ℤ := (core).deg (m, q)
  have hnn' : n + 1 = n' := by
    dsimp only [n, n',
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
    omega
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  let γIdx :
      ComposableArrows.mk₁
          (homOfLE (show (core).i₂ (m, q) ≤ (core).i₂ (m + 1, q) by
            change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
            simp)) ≅
        ComposableArrows.mk₁
          (homOfLE ((core).le₁₂ (m + 1, q))) :=
    ComposableArrows.isoMk₁ (eqToIso hmid) (Iso.refl _)
  have hpage :=
    B.partialTotalSpectralObject.spectralSequence_first_page_d_eq core
      (m + 1, q) (m, q)
      (coreE₁IncreasingHomologicalNat_rel_succ m q)
      ((core).i₁ (m, q)) ((core).i₂ (m, q))
      ((core).i₂ (m + 1, q)) rfl hmid rfl n n' rfl hnn'
  let ePageSource : P₁.X (m + 1, q) ≅
      (B.partialTotalSpectralObject.H n).obj
        (ComposableArrows.mk₁ (homOfLE ((core).le₁₂ (m + 1, q)))) :=
    B.partialTotalSpectralObject.spectralSequenceFirstPageXIso core
      (m + 1, q) ((core).i₁ (m + 1, q))
      ((core).i₂ (m + 1, q)) rfl rfl n rfl
  let ePageSourceCore :=
    B.partialTotalSpectralObject.spectralSequenceFirstPageXIso core
      (m + 1, q) ((core).i₂ (m, q))
      ((core).i₂ (m + 1, q)) hmid rfl n rfl
  have hPageSource :
      ePageSource.inv ≫ ePageSourceCore.hom =
        (B.partialTotalSpectralObject.H n).map γIdx.inv := by
    have hAux (j : EInt) (hj : j = (core).i₁ (m + 1, q)) :
        let γj :
            ComposableArrows.mk₁
                (homOfLE ((core).le₁₂' (m + 1, q) hj rfl)) ≅
              ComposableArrows.mk₁
                (homOfLE ((core).le₁₂ (m + 1, q))) :=
          ComposableArrows.isoMk₁ (eqToIso hj) (Iso.refl _)
        ePageSource.inv ≫
            (B.partialTotalSpectralObject.spectralSequenceFirstPageXIso core
              (m + 1, q) j ((core).i₂ (m + 1, q)) hj rfl n rfl).hom =
          (B.partialTotalSpectralObject.H n).map γj.inv := by
      dsimp only
      subst j
      dsimp only [ePageSource]
      rw [Iso.inv_hom_id]
      rw [← (B.partialTotalSpectralObject.H n).map_id]
      apply (B.partialTotalSpectralObject.H n).congr_map
      subsingleton
    let γMid :
        ComposableArrows.mk₁
            (homOfLE ((core).le₁₂' (m + 1, q) hmid rfl)) ≅
      ComposableArrows.mk₁
            (homOfLE ((core).le₁₂ (m + 1, q))) :=
      ComposableArrows.isoMk₁ (eqToIso hmid) (Iso.refl _)
        (by subsingleton)
    calc
      _ = (B.partialTotalSpectralObject.H n).map γMid.inv := by
        exact hAux ((core).i₂ (m, q)) hmid
      _ = (B.partialTotalSpectralObject.H n).map γIdx.inv := by
        apply (B.partialTotalSpectralObject.H n).congr_map
        apply ComposableArrows.hom_ext₁ <;> subsingleton
  rw [partialTotalE₁RowDifferential, hpage]
  dsimp only [partialTotalSpectralSequenceFirstPageRowIso,
    Iso.trans_inv, Iso.trans_hom]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [hPageSource]
  slice_lhs 5 6 => rw [Iso.inv_hom_id]
  simp only [Category.id_comp]
  slice_lhs 2 5 => erw [B.partialTotalE₁_delta_conjugation m q]
  exact partialTotalFourMiddleEq
    (B.partialTotalE₁_mappingConeDifferential_eq_connecting m q hnn')

/-- First-page differential equals horizontal row homology.

For natural `m` and `q`, `B.partialTotalE₁RowDifferential m q` equals the homology map induced
by the horizontal degree-one cocycle between the extended signed rows `m + 1` and `m`. -/
@[reassoc]
theorem partialTotalE₁RowDifferential_eq_horizontalRowHomology
    (m q : ℕ) :
    B.partialTotalE₁RowDifferential m q =
      B.partialTotalHorizontalRowHomology m q :=
  (B.partialTotalE₁RowDifferential_eq_connecting m q).trans
    (B.partialTotalE₁ConnectingDifferential_eq_horizontalRowHomology m q)

/-- Vertical homology with the first-page horizontal sign.

For fixed natural `q`, this horizontal chain complex has term `H_q(B.X p)` in degree `p` and
differential `ε(q) • H_q(B.d p p')`, where `ε(q) = (ComplexShape.down ℕ).ε q = (-1 : ℤˣ)^q`.
The sign acts on morphisms in the preadditive structure of the abelian category. -/
noncomputable def signedVerticalHomologyComplex (q : ℕ) :
    ChainComplex C ℕ where
  X p := (B.verticalHomologyComplex q).X p
  d p p' := (ComplexShape.down ℕ).ε q •
    (B.verticalHomologyComplex q).d p p'
  shape p p' h := by
    rw [HomologicalComplex.shape _ _ _ h, smul_zero]
  d_comp_d' p p' p'' hp hp' := by
    simp only [Linear.units_smul_comp, Linear.comp_units_smul,
      HomologicalComplex.d_comp_d, smul_zero]

/-- Terms of the signed vertical-homology complex.

The degree-`p` object of `B.signedVerticalHomologyComplex q` is `H_q(B.X p)`. -/
@[simp]
theorem signedVerticalHomologyComplex_X (p q : ℕ) :
    (B.signedVerticalHomologyComplex q).X p = (B.X p).homology q :=
  rfl

/-- Differential of the signed vertical-homology complex.

For natural `p`, `p'`, and `q`, the differential from degree `p` to `p'` is `ε(q) •
HomologicalComplex.homologyMap (B.d p p') q`, with `ε(q) = (-1 : ℤˣ)^q`. -/
@[simp]
theorem signedVerticalHomologyComplex_d (p p' q : ℕ) :
    (B.signedVerticalHomologyComplex q).d p p' =
      (ComplexShape.down ℕ).ε q •
        HomologicalComplex.homologyMap (B.d p p') q :=
  rfl

/-- Removing the constant first-page horizontal sign.

The signed vertical-homology complex at `q` is isomorphic to the ordinary horizontal complex
`B.verticalHomologyComplex q`. Its component in horizontal degree `p` multiplies by `ε(q)^p =
(-1 : ℤˣ)^(q*p)`. -/
noncomputable def signedVerticalHomologyIso (q : ℕ) :
    B.signedVerticalHomologyComplex q ≅ B.verticalHomologyComplex q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => ((ComplexShape.down ℕ).ε q) ^ p • Iso.refl _)
    (fun i j hij => by
      change j + 1 = i at hij
      subst i
      change
        (((ComplexShape.down ℕ).ε q) ^ (j + 1) • 𝟙 _) ≫
            (B.verticalHomologyComplex q).d (j + 1) j =
          ((ComplexShape.down ℕ).ε q •
              (B.verticalHomologyComplex q).d (j + 1) j) ≫
            (((ComplexShape.down ℕ).ε q) ^ j • 𝟙 _)
      simp only [Linear.units_smul_comp, Linear.comp_units_smul,
        Category.id_comp, Category.comp_id, smul_smul, pow_succ])

/-- Forward component of the horizontal sign-removal isomorphism.

In horizontal degree `p`, the forward component of `B.signedVerticalHomologyIso q` is `ε(q)^p
• 𝟙 (H_q(B.X p))`. -/
@[simp]
theorem signedVerticalHomologyIso_hom_f (p q : ℕ) :
    (B.signedVerticalHomologyIso q).hom.f p =
      ((ComplexShape.down ℕ).ε q) ^ p •
        𝟙 ((B.X p).homology q) := by
  rfl

/-- Inverse component of the horizontal sign-removal isomorphism.

In horizontal degree `p`, the inverse component of `B.signedVerticalHomologyIso q` is
`(ε(q)^p)⁻¹ • 𝟙 (H_q(B.X p))`. -/
@[simp]
theorem signedVerticalHomologyIso_inv_f (p q : ℕ) :
    (B.signedVerticalHomologyIso q).inv.f p =
      (((ComplexShape.down ℕ).ε q) ^ p)⁻¹ •
        𝟙 ((B.X p).homology q) := by
  rfl

private theorem epsilon_down_succ (p : ℕ) :
    (ComplexShape.down ℕ).ε (p + 1) =
      -(ComplexShape.down ℕ).ε p := by
  have h := ComplexShape.ε_succ
    (c := ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl)
  have h' := congrArg Neg.neg h
  simpa only [neg_neg] using h'.symm

private theorem epsilon_down_succ_pow (p q : ℕ) :
    ((ComplexShape.down ℕ).ε (p + 1)) ^ q =
      (ComplexShape.down ℕ).ε q *
        ((ComplexShape.down ℕ).ε p) ^ q := by
  simp only [ComplexShape.ε_down_ℕ, pow_add, pow_one, mul_pow]
  rw [mul_comm]

/-- Horizontal chain map between signed vertical rows.

The horizontal map from `B.signedRow (p + 1)` to `B.signedRow p` has vertical-degree-`q`
component `ε(q) • (B.d (p + 1) p).f q`. This degree-dependent sign makes the map commute with
the different vertical signs in the two signed rows. -/
noncomputable def partialTotalHorizontalSignedRowMap (p : ℕ) :
    B.signedRow (p + 1) ⟶ B.signedRow p where
  f q := (ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q
  comm' q q' h := by
    have hp : (ComplexShape.down ℕ).ε (p + 1) =
        -(ComplexShape.down ℕ).ε p := epsilon_down_succ p
    have hq : (ComplexShape.down ℕ).ε q =
        -(ComplexShape.down ℕ).ε q' := by
      have h₀ := ComplexShape.ε_succ (c := ComplexShape.down ℕ) h
      have h₁ := congrArg Neg.neg h₀
      simpa only [neg_neg] using h₁.symm
    change
      ((ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q) ≫
          ((ComplexShape.down ℕ).ε p • (B.X p).d q q') =
        ((ComplexShape.down ℕ).ε (p + 1) •
            (B.X (p + 1)).d q q') ≫
          ((ComplexShape.down ℕ).ε q' • (B.d (p + 1) p).f q')
    simp only [Linear.units_smul_comp,
      Linear.comp_units_smul, smul_smul]
    rw [(B.d (p + 1) p).comm]
    rw [hp, hq]
    have hscalar :
        (ComplexShape.down ℕ).ε p * (-(ComplexShape.down ℕ).ε q') =
          (ComplexShape.down ℕ).ε q' *
            (-(ComplexShape.down ℕ).ε p) := by
      rw [mul_neg, mul_neg, mul_comm]
    rw [hscalar]

/-- Component of the signed horizontal row map.

For natural `p` and `q`, the degree-`q` component of `B.partialTotalHorizontalSignedRowMap p`
is `ε(q) • (B.d (p + 1) p).f q`. -/
@[simp]
theorem partialTotalHorizontalSignedRowMap_f (p q : ℕ) :
    (B.partialTotalHorizontalSignedRowMap p).f q =
      (ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q :=
  rfl

/-- Signed horizontal row map agrees with the bicomplex map.

Compose the signed horizontal map with the isomorphism from signed row `p` to `B.X p`. This
equals the signed-row isomorphism at `p + 1` followed by `B.d (p + 1) p`. -/
@[reassoc]
theorem partialTotalHorizontalSignedRowMap_comp_signedRowIso (p : ℕ) :
    B.partialTotalHorizontalSignedRowMap p ≫
        (B.signedRowIso p).hom =
      (B.signedRowIso (p + 1)).hom ≫ B.d (p + 1) p := by
  ext q
  change
    ((ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q) ≫
        (((ComplexShape.down ℕ).ε p) ^ q • 𝟙 _) =
      (((ComplexShape.down ℕ).ε (p + 1)) ^ q • 𝟙 _) ≫
        (B.d (p + 1) p).f q
  simp only [
    Linear.units_smul_comp, Linear.comp_units_smul,
    Category.id_comp, Category.comp_id, smul_smul]
  have hscalar :
      ((ComplexShape.down ℕ).ε p) ^ q *
          (ComplexShape.down ℕ).ε q =
        ((ComplexShape.down ℕ).ε (p + 1)) ^ q := by
    rw [epsilon_down_succ_pow]
    exact mul_comm _ _
  rw [hscalar]

private theorem partialTotalHorizontalRowShift_homology_coordinate
    (p q : ℕ) :
    let ePlus : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
      ComplexShape.embeddingDown'Add 1 (p + 1)
    let eZero : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
      ComplexShape.embeddingDown'Add 1 p
    let NPlus := p + 1 + q
    let NZero := p + q
    let F := B.partialTotalHorizontalSignedRowMap p
    B.partialTotalHorizontalRowHomology p q ≫
        ((B.signedRow p).extendHomologyIso eZero
          (show eZero.f q = NZero by
            change q + p = p + q
            omega)).hom =
      (ComplexShape.down ℕ).ε q •
        (HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap F ePlus) NPlus ≫
          ((B.signedRow p).extendHomologyIso ePlus
            (show ePlus.f q = NPlus by
              change q + (p + 1) = p + 1 + q
              omega)).hom) := by
  let eNat : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingDownNat
  let ePlus : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add 1 (p + 1)
  let eZero : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add 1 p
  let NPlus : ℕ := p + 1 + q
  let NZero : ℕ := p + q
  let nPlus : ℤ := -((NPlus : ℕ) : ℤ)
  let nZero : ℤ := -((NZero : ℕ) : ℤ)
  have hNatPlus : eNat.f NPlus = nPlus := rfl
  have hNatZero : eNat.f NZero = nZero := rfl
  have hRowPlus : ePlus.f q = NPlus := by
    change q + (p + 1) = p + 1 + q
    omega
  have hRowZero : eZero.f q = NZero := by
    change q + p = p + q
    omega
  have hN : NZero + 1 = NPlus := by
    dsimp only [NZero, NPlus]
    omega
  have hShift : 1 + nPlus = nZero := by
    dsimp only [nPlus, nZero, NPlus, NZero]
    omega
  have hShiftX : nZero = nPlus + 1 := by
    dsimp only [nPlus, nZero, NPlus, NZero]
    omega
  have hnextPlus : (ComplexShape.up ℤ).next nPlus = nPlus + 1 := by
    exact CochainComplex.next ℤ nPlus
  have hnextZero : (ComplexShape.up ℤ).next nZero = nZero + 1 := by
    exact CochainComplex.next ℤ nZero
  let Kext : CochainComplex C ℤ := (B.totalRow (p + 1)).extend eNat
  let Lext : CochainComplex C ℤ := (B.totalRow p).extend eNat
  let z : Kext ⟶ Lext⟦(1 : ℤ)⟧ := B.partialTotalHorizontalRowShift p
  let F : B.signedRow (p + 1) ⟶ B.signedRow p := B.partialTotalHorizontalSignedRowMap p
  let xRowPlus : (B.totalRow (p + 1)).X NPlus ≅ (B.X (p + 1)).X q :=
    B.totalRowXIso (p + 1) q NPlus (by rfl)
  let xRowZero : (B.totalRow p).X NZero ≅ (B.X p).X q :=
    B.totalRowXIso p q NZero (by rfl)
  let eNatPlus := (B.totalRow (p + 1)).extendHomologyIso
    eNat hNatPlus
  let eNatZero := (B.totalRow p).extendHomologyIso
    eNat hNatZero
  let eRowPlusSource : (B.totalRow (p + 1)).homology NPlus ≅
      (B.signedRow (p + 1)).homology q :=
    (B.signedRow (p + 1)).extendHomologyIso ePlus hRowPlus
  let eRowZero : (B.totalRow p).homology NZero ≅ (B.signedRow p).homology q :=
    (B.signedRow p).extendHomologyIso eZero hRowZero
  let eRowPlusTarget := (B.signedRow p).extendHomologyIso
    ePlus hRowPlus
  let cNatPlus := (B.totalRow (p + 1)).extendCyclesIso
    eNat hNatPlus
  let cNatZero := (B.totalRow p).extendCyclesIso eNat hNatZero
  let cRowPlusSource : (B.totalRow (p + 1)).cycles NPlus ≅
      (B.signedRow (p + 1)).cycles q :=
    (B.signedRow (p + 1)).extendCyclesIso ePlus hRowPlus
  let cRowZero : (B.totalRow p).cycles NZero ≅ (B.signedRow p).cycles q :=
    (B.signedRow p).extendCyclesIso eZero hRowZero
  let δ : Kext.homology nPlus ⟶ Lext.homology nZero :=
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      z nPlus nZero (by dsimp [nPlus, nZero, NPlus, NZero]; omega)
  change B.partialTotalHorizontalRowHomology p q ≫ eRowZero.hom =
    (ComplexShape.down ℕ).ε q •
      (HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap F ePlus) NPlus ≫
        eRowPlusTarget.hom)
  have hFextNat :
      HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap F ePlus) NPlus ≫
          eRowPlusTarget.hom =
        eRowPlusSource.hom ≫
          HomologicalComplex.homologyMap F q := by
    exact HomologicalComplex.extendHomologyIso_hom_naturality
      (φ := F) (e := ePlus) (hj' := hRowPlus)
  erw [hFextNat]
  have hHorizontal : B.partialTotalHorizontalRowHomology p q =
      eNatPlus.inv ≫ δ ≫ eNatZero.hom :=
    B.partialTotalHorizontalRowHomology_eq p q
  rw [hHorizontal]
  simp only [Category.assoc]
  change eNatPlus.inv ≫ δ ≫ eNatZero.hom ≫ eRowZero.hom =
    (ComplexShape.down ℕ).ε q •
      (eRowPlusSource.hom ≫ HomologicalComplex.homologyMap F q)
  rw [← cancel_epi eNatPlus.hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← cancel_epi
    (((B.totalRow (p + 1)).extend eNat).homologyπ nPlus)]
  have hδ : δ = HomologicalComplex.homologyMap z nPlus ≫
      (partialTotalShiftHomologyIso Lext 1 nPlus nZero hShift).hom :=
    partialTotalShiftMapHomology (n := (1 : ℤ)) z nPlus nZero hShift
  rw [hδ]
  slice_lhs 1 2 =>
    rw [HomologicalComplex.homologyπ_naturality]
  let x : Kext.cycles nPlus ⟶ (Lext⟦(1 : ℤ)⟧).X nPlus :=
    Kext.iCycles nPlus ≫ z.f nPlus
  have hx : x ≫ (Lext⟦(1 : ℤ)⟧).d nPlus (nPlus + 1) = 0 := by
    dsimp only [x]
    rw [Category.assoc, z.comm, ← Category.assoc,
      Kext.iCycles_d, zero_comp]
  have hcycles :
      HomologicalComplex.cyclesMap z nPlus =
        (Lext⟦(1 : ℤ)⟧).liftCycles x (nPlus + 1) hnextPlus hx := by
    rw [← cancel_mono ((Lext⟦(1 : ℤ)⟧).iCycles nPlus),
      HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i]
  have hz := B.partialTotalHorizontalRowShift_f_comp_shiftIso p NZero
  have hF := B.partialTotalHorizontalRowF_eq p q
  have hIndex : eNat.f (NZero + 1) = nPlus := by
    rw [hN, hNatPlus]
  have hComponent :
      Kext.iCycles nPlus ≫ z.f nPlus ≫
          (CochainComplex.shiftFunctorObjXIso
            Lext 1 nPlus nZero hShiftX).hom ≫
          ((B.totalRow p).extendXIso eNat hNatZero).hom ≫
          xRowZero.hom =
        (ComplexShape.down ℕ).ε q •
          (Kext.iCycles nPlus ≫
            ((B.totalRow (p + 1)).extendXIso eNat hNatPlus).hom ≫
            xRowPlus.hom ≫
            ((ComplexShape.down ℕ).ε q •
              (B.d (p + 1) p).f q)) := by
    let nrPlus := eNat.f (NZero + 1)
    let nrZero := eNat.f NZero
    have hShiftRow : nrZero = nrPlus + 1 := by
      change -((NZero : ℕ) : ℤ) =
        -(((NZero + 1 : ℕ) : ℤ)) + 1
      omega
    let xRowPlus' := B.totalRowXIso (p + 1) q (NZero + 1) (by
      dsimp only [NZero]
      omega)
    have hComponentRow :
        Kext.iCycles nrPlus ≫ z.f nrPlus ≫
            (CochainComplex.shiftFunctorObjXIso
              Lext 1 nrPlus nrZero hShiftRow).hom ≫
            ((B.totalRow p).extendXIso eNat rfl).hom ≫
            xRowZero.hom =
          (ComplexShape.down ℕ).ε q •
            (Kext.iCycles nrPlus ≫
              ((B.totalRow (p + 1)).extendXIso eNat rfl).hom ≫
              xRowPlus'.hom ≫
              ((ComplexShape.down ℕ).ε q •
                (B.d (p + 1) p).f q)) := by
      slice_lhs 2 3 => rw [hz]
      simp only [Category.assoc]
      slice_lhs 4 5 => rw [Iso.inv_hom_id]
      slice_lhs 3 4 => rw [Category.comp_id]
      rw [hF]
      simp only [Category.assoc]
      slice_lhs 5 6 => rw [Iso.inv_hom_id]
      slice_lhs 4 5 => rw [Category.comp_id]
      let g := Kext.iCycles nrPlus ≫
        ((B.totalRow (p + 1)).extendXIso eNat rfl).hom ≫
        xRowPlus'.hom
      have hg : g ≫ (B.d (p + 1) p).f q =
          (ComplexShape.down ℕ).ε q •
            (g ≫ ((ComplexShape.down ℕ).ε q •
              (B.d (p + 1) p).f q)) := by
        rw [Linear.comp_units_smul, smul_smul,
          Int.units_mul_self, one_smul]
      dsimp only [g, xRowPlus', eNat] at hg ⊢
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hg
    let D := {n : ℕ // NZero + 1 = n}
    let dMain : D := ⟨NPlus, hN⟩
    let dRow : D := ⟨NZero + 1, rfl⟩
    let nAt (d : D) : ℤ := eNat.f d.1
    have hShiftAt (d : D) : nZero = nAt d + 1 := by
      change -((NZero : ℕ) : ℤ) = -((d.1 : ℕ) : ℤ) + 1
      have hd := d.2
      omega
    let xRowAt (d : D) := B.totalRowXIso (p + 1) q d.1 (by
      have hd := d.2
      dsimp only [NZero] at hd
      omega)
    let lhsAt (d : D) : Kext.cycles (nAt d) ⟶ (B.X p).X q :=
      Kext.iCycles (nAt d) ≫ z.f (nAt d) ≫
        (CochainComplex.shiftFunctorObjXIso
          Lext 1 (nAt d) nZero (hShiftAt d)).hom ≫
        ((B.totalRow p).extendXIso eNat hNatZero).hom ≫
        xRowZero.hom
    let rhsAt (d : D) : Kext.cycles (nAt d) ⟶ (B.X p).X q :=
      (ComplexShape.down ℕ).ε q •
        (Kext.iCycles (nAt d) ≫
          ((B.totalRow (p + 1)).extendXIso eNat rfl).hom ≫
          (xRowAt d).hom ≫
          ((ComplexShape.down ℕ).ε q •
            (B.d (p + 1) p).f q))
    have hRow : lhsAt dRow = rhsAt dRow := by
      change
        Kext.iCycles nrPlus ≫ z.f nrPlus ≫
            (CochainComplex.shiftFunctorObjXIso
              Lext 1 nrPlus nrZero hShiftRow).hom ≫
            ((B.totalRow p).extendXIso eNat rfl).hom ≫
            xRowZero.hom =
          (ComplexShape.down ℕ).ε q •
            (Kext.iCycles nrPlus ≫
              ((B.totalRow (p + 1)).extendXIso eNat rfl).hom ≫
              xRowPlus'.hom ≫
              ((ComplexShape.down ℕ).ε q •
                (B.d (p + 1) p).f q))
      exact hComponentRow
    have hd : dMain = dRow := by
      apply Subtype.ext
      exact hN.symm
    change lhsAt dMain = rhsAt dMain
    exact partialTotalTransportHomEquality lhsAt rhsAt hd hRow
  have hRowZeroICycles :
      cRowZero.hom ≫ (B.signedRow p).iCycles q =
        (B.totalRow p).iCycles NZero ≫
          xRowZero.hom := by
    have h := HomologicalComplex.extendCyclesIso_hom_iCycles
      (K := B.signedRow p) (e := eZero) (hj' := hRowZero)
    change cRowZero.hom ≫ (B.signedRow p).iCycles q =
      (B.totalRow p).iCycles NZero ≫ xRowZero.hom at h
    exact h
  have hRowPlusICycles :
      cRowPlusSource.hom ≫ (B.signedRow (p + 1)).iCycles q =
        (B.totalRow (p + 1)).iCycles NPlus ≫
          xRowPlus.hom := by
    have h := HomologicalComplex.extendCyclesIso_hom_iCycles
      (K := B.signedRow (p + 1)) (e := ePlus) (hj' := hRowPlus)
    change cRowPlusSource.hom ≫ (B.signedRow (p + 1)).iCycles q =
      (B.totalRow (p + 1)).iCycles NPlus ≫ xRowPlus.hom at h
    exact h
  have hRowZeroHomologyπ :
      (B.totalRow p).homologyπ NZero ≫ eRowZero.hom =
        cRowZero.hom ≫ (B.signedRow p).homologyπ q := by
    simpa only [totalRow] using
      (HomologicalComplex.homologyπ_extendHomologyIso_hom
        (K := B.signedRow p) (e := eZero) (hj' := hRowZero))
  have hRowPlusHomologyπ :
      (B.totalRow (p + 1)).homologyπ NPlus ≫
          eRowPlusSource.hom =
        cRowPlusSource.hom ≫
          (B.signedRow (p + 1)).homologyπ q := by
    simpa only [totalRow] using
      (HomologicalComplex.homologyπ_extendHomologyIso_hom
        (K := B.signedRow (p + 1)) (e := ePlus) (hj' := hRowPlus))
  have hLeftCycles
      (hy :
        (x ≫ (CochainComplex.shiftFunctorObjXIso
          Lext 1 nPlus nZero hShiftX).hom) ≫
            Lext.d nZero (nZero + 1) = 0) :
      Lext.liftCycles
          (x ≫ (CochainComplex.shiftFunctorObjXIso
            Lext 1 nPlus nZero hShiftX).hom)
          (nZero + 1) hnextZero hy ≫
          cNatZero.hom ≫ cRowZero.hom ≫
          (B.signedRow p).iCycles q =
        x ≫
          (CochainComplex.shiftFunctorObjXIso
            Lext 1 nPlus nZero hShiftX).hom ≫
          ((B.totalRow p).extendXIso eNat hNatZero).hom ≫
          xRowZero.hom := by
    dsimp only [signedRow]
    have hNatZeroICycles :
        cNatZero.hom ≫ (B.totalRow p).iCycles NZero =
          Lext.iCycles nZero ≫ ((B.totalRow p).extendXIso eNat hNatZero).hom :=
      HomologicalComplex.extendCyclesIso_hom_iCycles
        (K := B.totalRow p) (e := eNat) (hj' := hNatZero)
    have hLift :
        Lext.liftCycles
            (x ≫ (CochainComplex.shiftFunctorObjXIso Lext 1 nPlus nZero hShiftX).hom)
            (nZero + 1) hnextZero hy ≫ Lext.iCycles nZero =
          x ≫ (CochainComplex.shiftFunctorObjXIso Lext 1 nPlus nZero hShiftX).hom := by
      rw [HomologicalComplex.liftCycles_i]
    calc
      _ = Lext.liftCycles
          (x ≫ (CochainComplex.shiftFunctorObjXIso Lext 1 nPlus nZero hShiftX).hom)
          (nZero + 1) hnextZero hy ≫
            cNatZero.hom ≫ (B.totalRow p).iCycles NZero ≫ xRowZero.hom := by
        simpa only [Category.assoc, signedRow] using
          congrArg (fun f => Lext.liftCycles
            (x ≫ (CochainComplex.shiftFunctorObjXIso Lext 1 nPlus nZero hShiftX).hom)
            (nZero + 1) hnextZero hy ≫ cNatZero.hom ≫ f) hRowZeroICycles
      _ = Lext.liftCycles
          (x ≫ (CochainComplex.shiftFunctorObjXIso Lext 1 nPlus nZero hShiftX).hom)
          (nZero + 1) hnextZero hy ≫ Lext.iCycles nZero ≫
            ((B.totalRow p).extendXIso eNat hNatZero).hom ≫ xRowZero.hom := by
        simpa only [Category.assoc] using
          congrArg (fun f => Lext.liftCycles
            (x ≫ (CochainComplex.shiftFunctorObjXIso Lext 1 nPlus nZero hShiftX).hom)
            (nZero + 1) hnextZero hy ≫ f ≫ xRowZero.hom) hNatZeroICycles
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ ((B.totalRow p).extendXIso eNat hNatZero).hom ≫
            xRowZero.hom) hLift
  have hRightCycles :
      cNatPlus.hom ≫ cRowPlusSource.hom ≫
          HomologicalComplex.cyclesMap F q ≫
          (B.signedRow p).iCycles q =
        Kext.iCycles nPlus ≫
          ((B.totalRow (p + 1)).extendXIso eNat hNatPlus).hom ≫
          xRowPlus.hom ≫
          ((ComplexShape.down ℕ).ε q •
            (B.d (p + 1) p).f q) := by
    dsimp only [signedRow]
    have hNatPlusICycles :
        cNatPlus.hom ≫ (B.totalRow (p + 1)).iCycles NPlus =
          Kext.iCycles nPlus ≫
            ((B.totalRow (p + 1)).extendXIso eNat hNatPlus).hom :=
      HomologicalComplex.extendCyclesIso_hom_iCycles
        (K := B.totalRow (p + 1)) (e := eNat) (hj' := hNatPlus)
    have hFICycles :
        HomologicalComplex.cyclesMap F q ≫ (B.signedRow p).iCycles q =
          (B.signedRow (p + 1)).iCycles q ≫
            ((ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q) := by
      have hf : F.f q = (ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q :=
        B.partialTotalHorizontalSignedRowMap_f p q
      exact (HomologicalComplex.cyclesMap_i F q).trans
        (congrArg (fun t => (B.signedRow (p + 1)).iCycles q ≫ t) hf)
    calc
      _ = cNatPlus.hom ≫ cRowPlusSource.hom ≫
          (B.signedRow (p + 1)).iCycles q ≫
            ((ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q) := by
        simpa only [Category.assoc, signedRow] using
          congrArg (fun f => cNatPlus.hom ≫ cRowPlusSource.hom ≫ f) hFICycles
      _ = cNatPlus.hom ≫ (B.totalRow (p + 1)).iCycles NPlus ≫
          xRowPlus.hom ≫ ((ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q) := by
        simpa only [Category.assoc, signedRow] using
          congrArg (fun f => cNatPlus.hom ≫ f ≫
            ((ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q)) hRowPlusICycles
      _ = Kext.iCycles nPlus ≫
          ((B.totalRow (p + 1)).extendXIso eNat hNatPlus).hom ≫
            xRowPlus.hom ≫ ((ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q) := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ xRowPlus.hom ≫
            ((ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q)) hNatPlusICycles
  have hCycle
      (hy :
        (x ≫ (CochainComplex.shiftFunctorObjXIso
          Lext 1 nPlus nZero hShiftX).hom) ≫
            Lext.d nZero (nZero + 1) = 0) :
      Lext.liftCycles
          (x ≫ (CochainComplex.shiftFunctorObjXIso
            Lext 1 nPlus nZero hShiftX).hom)
          (nZero + 1) hnextZero hy ≫
          cNatZero.hom ≫ cRowZero.hom =
        (ComplexShape.down ℕ).ε q •
          (cNatPlus.hom ≫ cRowPlusSource.hom ≫
            HomologicalComplex.cyclesMap F q) := by
    let a := Lext.liftCycles
      (x ≫ (CochainComplex.shiftFunctorObjXIso Lext 1 nPlus nZero hShiftX).hom)
      (nZero + 1) hnextZero hy ≫ cNatZero.hom ≫ cRowZero.hom
    let b := cNatPlus.hom ≫ cRowPlusSource.hom
    let k := HomologicalComplex.cyclesMap F q
    let i : (B.signedRow p).cycles q ⟶ (B.X p).X q :=
      (B.signedRow p).iCycles q ≫ eqToHom (HomologicalComplex₂.signedRow_X B p q)
    let : Mono i := by dsimp only [i]; infer_instance
    have hout := partialTotalCycleCoordinateComm (D := C)
      ((ComplexShape.down ℕ).ε q) hComponent a b k i
      (by
        dsimp only [a, i]
        rw [partialTotalSignedRowXHom]
        have hpost := congrArg
          (fun z => z ≫ eqToHom (HomologicalComplex₂.signedRow_X B p q))
          (hLeftCycles hy)
        rw [partialTotalSignedRowXHom] at hpost
        have hnormalized := hpost.trans (Category.comp_id _)
        simpa only [Category.assoc, Category.comp_id, x] using hnormalized)
      (by
        dsimp only [b, k, i]
        rw [partialTotalSignedRowXHom]
        have hpost := congrArg
          (fun z => z ≫ eqToHom (HomologicalComplex₂.signedRow_X B p q)) hRightCycles
        rw [partialTotalSignedRowXHom] at hpost
        have hnormalized := hpost.trans (Category.comp_id _)
        simpa only [Category.assoc, Category.comp_id] using hnormalized)
    simpa only [a, b, k, Category.assoc] using hout
  have hRightHomology :
      Kext.homologyπ nPlus ≫ eNatPlus.hom ≫
          eRowPlusSource.hom ≫
          HomologicalComplex.homologyMap F q =
        cNatPlus.hom ≫ cRowPlusSource.hom ≫
          HomologicalComplex.cyclesMap F q ≫
          (B.signedRow p).homologyπ q := by
    slice_lhs 1 2 =>
      rw [HomologicalComplex.homologyπ_extendHomologyIso_hom]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [hRowPlusHomologyπ]
    simp only [Category.assoc]
    slice_lhs 3 4 =>
      rw [HomologicalComplex.homologyπ_naturality]
  rw [hcycles]
  obtain ⟨hy, hShiftCycles⟩ :=
    partialTotalLiftCyclesShiftHomology (n := (1 : ℤ)) (i := nPlus)
      Lext x (nPlus + 1) hnextPlus hx nZero hShift (nZero + 1) hnextZero
  have hShiftTail :
      (Lext⟦(1 : ℤ)⟧).liftCycles x (nPlus + 1) hnextPlus hx ≫
          (Lext⟦(1 : ℤ)⟧).homologyπ nPlus ≫
          (partialTotalShiftHomologyIso Lext 1 nPlus nZero hShift).hom ≫
          eNatZero.hom ≫ eRowZero.hom =
        Lext.liftCycles
            (x ≫ (CochainComplex.shiftFunctorObjXIso Lext 1 nPlus nZero hShiftX).hom)
            (nZero + 1) hnextZero hy ≫
          Lext.homologyπ nZero ≫ eNatZero.hom ≫ eRowZero.hom := by
    simpa only [Category.assoc] using
      congrArg (fun t : Kext.cycles nPlus ⟶ Lext.homology nZero =>
        t ≫ eNatZero.hom ≫ eRowZero.hom) hShiftCycles
  simp only [Category.assoc]
  rw [hShiftTail]
  slice_lhs 2 3 =>
    rw [HomologicalComplex.homologyπ_extendHomologyIso_hom]
  simp only [Category.assoc]
  rw [hRowZeroHomologyπ]
  simp only [Linear.comp_units_smul]
  rw [hRightHomology]
  slice_lhs 1 3 => rw [hCycle]
  simp only [ComplexShape.ε_down_ℕ, Linear.units_smul_comp,
    Category.assoc]

/-- Horizontal row homology yields the signed vertical-homology differential.

Transport the horizontal row homology map from total degrees `p + 1 + q` and `p + q` to
vertical homology through `B.totalRowHomologyIso`. The resulting map is the differential from
`p + 1` to `p` in `B.signedVerticalHomologyComplex q`, including its factor `ε(q)`. -/
@[reassoc]
theorem partialTotalHorizontalRowHomology_totalRowHomologyIso
    (p q : ℕ) :
    B.partialTotalHorizontalRowHomology p q ≫
        (B.totalRowHomologyIso p q).hom =
      (B.totalRowHomologyIso (p + 1) q).hom ≫
        (B.signedVerticalHomologyComplex q).d (p + 1) p := by
  let ePlus : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add 1 (p + 1)
  let eZero : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add 1 p
  let NPlus : ℕ := p + 1 + q
  let NZero : ℕ := p + q
  let F : B.signedRow (p + 1) ⟶ B.signedRow p := B.partialTotalHorizontalSignedRowMap p
  have hRowPlus : ePlus.f q = NPlus := by
    change q + (p + 1) = p + 1 + q
    omega
  have hRowZero : eZero.f q = NZero := by
    change q + p = p + q
    omega
  let eRowPlusSource : (B.totalRow (p + 1)).homology NPlus ≅
      (B.signedRow (p + 1)).homology q :=
    (B.signedRow (p + 1)).extendHomologyIso ePlus hRowPlus
  let eRowPlusTarget :=
    (B.signedRow p).extendHomologyIso ePlus hRowPlus
  let eRowZero : (B.totalRow p).homology NZero ≅ (B.signedRow p).homology q :=
    (B.signedRow p).extendHomologyIso eZero hRowZero
  have hCoordinate :=
    B.partialTotalHorizontalRowShift_homology_coordinate p q
  have hFextNat :
      HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap F ePlus) NPlus ≫
          eRowPlusTarget.hom =
        eRowPlusSource.hom ≫
          HomologicalComplex.homologyMap F q := by
    exact HomologicalComplex.extendHomologyIso_hom_naturality
      (φ := F) (e := ePlus) (hj' := hRowPlus)
  have hMiddle :
      B.partialTotalHorizontalRowHomology p q ≫ eRowZero.hom =
        (ComplexShape.down ℕ).ε q •
          (eRowPlusSource.hom ≫
            HomologicalComplex.homologyMap F q) :=
    hCoordinate.trans
      (congrArg (fun f => (ComplexShape.down ℕ).ε q • f) hFextNat)
  have hSignedHomology :
      HomologicalComplex.homologyMap F q ≫
          (HomologicalComplex.homologyMapIso (B.signedRowIso p) q).hom =
        (HomologicalComplex.homologyMapIso
            (B.signedRowIso (p + 1)) q).hom ≫
          HomologicalComplex.homologyMap (B.d (p + 1) p) q := by
    have h := congrArg
      (fun f => HomologicalComplex.homologyMap f q)
      (B.partialTotalHorizontalSignedRowMap_comp_signedRowIso p)
    simpa only [HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMapIso_hom] using h
  have hTotalZero :
      (B.totalRowHomologyIso p q).hom =
        eRowZero.hom ≫
          (HomologicalComplex.homologyMapIso (B.signedRowIso p) q).hom := by
    rfl
  have hTotalPlus :
      (B.totalRowHomologyIso (p + 1) q).hom =
        eRowPlusSource.hom ≫
          (HomologicalComplex.homologyMapIso
            (B.signedRowIso (p + 1)) q).hom := by
    rfl
  let h : (B.totalRow (p + 1)).homology NPlus ⟶ (B.totalRow p).homology NZero :=
    B.partialTotalHorizontalRowHomology p q
  let r₀ : (B.signedRow (p + 1)).homology q ⟶ (B.X (p + 1)).homology q :=
    (HomologicalComplex.homologyMapIso (B.signedRowIso (p + 1)) q).hom
  let r₁ : (B.signedRow p).homology q ⟶ (B.X p).homology q :=
    (HomologicalComplex.homologyMapIso (B.signedRowIso p) q).hom
  let f : (B.signedRow (p + 1)).homology q ⟶ (B.signedRow p).homology q :=
    HomologicalComplex.homologyMap F q
  let g : (B.X (p + 1)).homology q ⟶ (B.X p).homology q :=
    HomologicalComplex.homologyMap (B.d (p + 1) p) q
  let dSigned : (B.X (p + 1)).homology q ⟶ (B.X p).homology q :=
    (B.signedVerticalHomologyComplex q).d (p + 1) p
  let e₀ : (B.totalRow (p + 1)).homology NPlus ≅ (B.X (p + 1)).homology q :=
    B.totalRowHomologyIso (p + 1) q
  let e₁ : (B.totalRow p).homology NZero ≅ (B.X p).homology q :=
    B.totalRowHomologyIso p q
  have h₀ : e₀.hom = eRowPlusSource.hom ≫ r₀ := hTotalPlus
  have h₁ : e₁.hom = eRowZero.hom ≫ r₁ := hTotalZero
  have hd : dSigned = (ComplexShape.down ℕ).ε q • g :=
    B.signedVerticalHomologyComplex_d (p + 1) p q
  have hsquare : h ≫ (eRowZero.hom ≫ r₁) =
      (eRowPlusSource.hom ≫ r₀) ≫ ((ComplexShape.down ℕ).ε q • g) :=
    partialTotalSignedCoordinateSquare ((ComplexShape.down ℕ).ε q)
      h eRowPlusSource eRowZero r₀ r₁ f g hMiddle hSignedHomology
  change h ≫ e₁.hom = e₀.hom ≫ dSigned
  calc
    h ≫ e₁.hom = h ≫ (eRowZero.hom ≫ r₁) := congrArg (fun k => h ≫ k) h₁
    _ = (eRowPlusSource.hom ≫ r₀) ≫ ((ComplexShape.down ℕ).ε q • g) := hsquare
    _ = e₀.hom ≫ dSigned :=
      congrArg₂ (fun a b => a ≫ b) h₀.symm hd.symm

private theorem partialTotalHorizontalRowHomology_totalRowHomologyIsoAtAux
    (p q nPlus nZero : ℕ)
    (hPlus : (p + 1) + q = nPlus)
    (hZero : p + q = nZero)
    (hShift :
      1 + ComplexShape.embeddingDownNat.f nPlus =
        ComplexShape.embeddingDownNat.f nZero) :
    let eNat := ComplexShape.embeddingDownNat
    let nPlus' : ℤ := eNat.f nPlus
    let nZero' : ℤ := eNat.f nZero
    let rAt :
        (B.totalRow (p + 1)).homology nPlus ⟶
          (B.totalRow p).homology nZero :=
      ((B.totalRow (p + 1)).extendHomologyIso eNat rfl).inv ≫
        (HomologicalComplex.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftMap
            (B.partialTotalHorizontalRowShift p) nPlus' nZero' hShift ≫
        ((B.totalRow p).extendHomologyIso eNat rfl).hom
    rAt ≫
        (B.totalRowHomologyIsoAt p q nZero hZero).hom =
      (B.totalRowHomologyIsoAt
          (p + 1) q nPlus hPlus).hom ≫
        (B.signedVerticalHomologyComplex q).d (p + 1) p := by
  subst nPlus
  subst nZero
  have hIsoPlus :
      B.totalRowHomologyIsoAt
          (p + 1) q ((p + 1) + q) rfl =
        B.totalRowHomologyIso (p + 1) q := by
    rfl
  have hIsoZero :
      B.totalRowHomologyIsoAt p q (p + q) rfl =
        B.totalRowHomologyIso p q := by
    rfl
  rw [hIsoPlus, hIsoZero]
  change B.partialTotalHorizontalRowHomology p q ≫
      (B.totalRowHomologyIso p q).hom =
    (B.totalRowHomologyIso (p + 1) q).hom ≫
      (B.signedVerticalHomologyComplex q).d (p + 1) p
  exact B.partialTotalHorizontalRowHomology_totalRowHomologyIso p q

private theorem partialTotalHorizontalRowHomology_totalRowHomologyIsoAt
    (p q : ℕ)
    (hPlus : (p + 1) + q = (q + p) + 1)
    (hZero : p + q = q + p) :
    let eNat := ComplexShape.embeddingDownNat
    let NZero := q + p
    let NPlus := NZero + 1
    let nPlus : ℤ := eNat.f NPlus
    let nZero : ℤ := eNat.f NZero
    let rAt :
        (B.totalRow (p + 1)).homology NPlus ⟶
          (B.totalRow p).homology NZero :=
      ((B.totalRow (p + 1)).extendHomologyIso eNat rfl).inv ≫
        (HomologicalComplex.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftMap
            (B.partialTotalHorizontalRowShift p) nPlus nZero (by
              change 1 + -((NPlus : ℕ) : ℤ) = -((NZero : ℕ) : ℤ)
              omega) ≫
        ((B.totalRow p).extendHomologyIso eNat rfl).hom
    rAt ≫
        (B.totalRowHomologyIsoAt p q NZero hZero).hom =
      (B.totalRowHomologyIsoAt
          (p + 1) q NPlus hPlus).hom ≫
        (B.signedVerticalHomologyComplex q).d (p + 1) p := by
  have hShift :
      1 + ComplexShape.embeddingDownNat.f (q + p + 1) =
        ComplexShape.embeddingDownNat.f (q + p) := by
    change 1 + -((q + p + 1 : ℕ) : ℤ) = -((q + p : ℕ) : ℤ)
    omega
  exact B.partialTotalHorizontalRowHomology_totalRowHomologyIsoAtAux
    p q (q + p + 1) (q + p) hPlus hZero hShift

/-- Homology of a fixed first-page row in bidegree coordinates.

Restrict the first page along `p ↦ (p, q)`. Its homology in horizontal degree `p` is
isomorphic to the homology of the full first-page complex at `(p, q)`. -/
noncomputable def partialTotalFirstPageRowRestrictionHomologyIso (p q : ℕ) :
    ((((B.partialTotalSpectralObject.spectralSequence core).page 1).restriction
        (partialTotalFirstPageRowEmbedding q)).homology p) ≅
      ((B.partialTotalSpectralObject.spectralSequence core).page 1).homology
        (p, q) := by
  let P₁ := (B.partialTotalSpectralObject.spectralSequence core).page 1
  let e := partialTotalFirstPageRowEmbedding q
  refine P₁.restrictionHomologyIsoAt e p ?_ ?_
  · apply (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).prev_eq'
    exact e.rel (by
      change p + 1 = (ComplexShape.down ℕ).prev p
      simp)
  · rcases p with _ | p
    · simp only [ChainComplex.next_nat_zero]
      apply (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).next_eq_self'
      intro z hz
      have hfst : (0 : ℤ) + (-1 : ℤ) = z.1 :=
        ((ComplexShape.spectralSequenceNat_rel_iff
          ⟨(-1 : ℤ), 0⟩ (0, q) z).mp hz).1
      omega
    · exact (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).next_eq'
        (e.rel (by
          simp only [ChainComplex.next_nat_succ]
          rfl))

private theorem partialTotalIsoCoordinatesComm
    {D : Type*} [Category D] {A₀ A₁ B₀ B₁ C₀ C₁ : D}
    (e₀ : A₀ ≅ B₀) (e₁ : A₁ ≅ B₁) (r₀ : B₀ ≅ C₀) (r₁ : B₁ ≅ C₁)
    (f : B₀ ⟶ B₁) (g : C₀ ⟶ C₁) (d : A₀ ⟶ A₁)
    (hrow : f ≫ r₁.hom = r₀.hom ≫ g)
    (hpage : d = e₀.hom ≫ f ≫ e₁.inv) :
    (e₀.hom ≫ r₀.hom) ≫ g = d ≫ (e₁.hom ≫ r₁.hom) :=
  (partialTotalIsoCoordinateComm e₀ e₁ r₀ r₁ f g hrow).trans
    (congrArg (fun t : A₀ ⟶ A₁ => t ≫ (e₁.hom ≫ r₁.hom)) hpage.symm)

private theorem partialTotalFirstPageRestrictionD
    (P : HomologicalComplex C (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩))
    (q p : ℕ) :
    (P.restriction (partialTotalFirstPageRowEmbedding q)).d (p + 1) p =
      P.d (p + 1, q) (p, q) := by
  let e := partialTotalFirstPageRowEmbedding q
  rw [P.restriction_d_eq e
    (show e.f (p + 1) = (p + 1, q) by rfl)
    (show e.f p = (p, q) by rfl)]
  change (𝟙 (P.X (p + 1, q))) ≫ P.d (p + 1, q) (p, q) ≫
    𝟙 (P.X (p, q)) = P.d (p + 1, q) (p, q)
  simp only [Category.id_comp, Category.comp_id]

private theorem partialTotalFirstPageCoordinateComm
    {D : Type*} [Category D] [Abelian D]
    (P : HomologicalComplex D (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩))
    (L : ChainComplex D ℕ) (q : ℕ) (Y : ℕ → D)
    (e : ∀ p, P.X (p, q) ≅ Y p) (r : ∀ p, Y p ≅ L.X p)
    (f : ∀ p, Y (p + 1) ⟶ Y p)
    (hpage : ∀ p, P.d (p + 1, q) (p, q) = (e (p + 1)).hom ≫ f p ≫ (e p).inv)
    (hrow : ∀ p, f p ≫ (r p).hom = (r (p + 1)).hom ≫ L.d (p + 1) p) :
    ∀ i j (_hij : (ComplexShape.down ℕ).Rel i j),
      (e i ≪≫ r i).hom ≫ L.d i j =
        (P.restriction (partialTotalFirstPageRowEmbedding q)).d i j ≫ (e j ≪≫ r j).hom := by
  intro i j hij
  change j + 1 = i at hij
  subst i
  have hd :
      (P.restriction (partialTotalFirstPageRowEmbedding q)).d (j + 1) j =
        (e (j + 1)).hom ≫ f j ≫ (e j).inv :=
    (partialTotalFirstPageRestrictionD (C := D) P q j).trans (hpage j)
  change ((e (j + 1)).hom ≫ (r (j + 1)).hom) ≫ L.d (j + 1) j =
    _ ≫ ((e j).hom ≫ (r j).hom)
  exact partialTotalIsoCoordinatesComm
    (e (j + 1)) (e j) (r (j + 1)) (r j) (f j) (L.d (j + 1) j)
    ((P.restriction (partialTotalFirstPageRowEmbedding q)).d (j + 1) j)
    (hrow j) hd

/-- First-page row as signed vertical homology.

At fixed vertical degree `q`, the first-page complex restricted to `p ↦ (p, q)` is isomorphic
to `B.signedVerticalHomologyComplex q`. The component at `p` is the first-page total-row
homology coordinate followed by the signed-row comparison with `H_q(B.X p)`. -/
noncomputable def partialTotalFirstPageSignedVerticalHomologyIso (q : ℕ) :
    @CategoryTheory.Iso (ChainComplex C ℕ) inferInstance
      (((B.partialTotalSpectralObject.spectralSequence core).page 1).restriction
        (partialTotalFirstPageRowEmbedding q))
      (B.signedVerticalHomologyComplex q) := by
  let P₁ : HomologicalComplex C
      (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩) :=
    (B.partialTotalSpectralObject.spectralSequence core).page 1
  let L : ChainComplex C ℕ := B.signedVerticalHomologyComplex q
  let Y : ℕ → C := fun p => (B.totalRow p).homology (p + q)
  let e : ∀ p, P₁.X (p, q) ≅ Y p :=
    fun p => B.partialTotalSpectralSequenceFirstPageRowIso p q
  have hLX : ∀ p, L.X p = (B.X p).homology q :=
    fun p => B.signedVerticalHomologyComplex_X p q
  let r : ∀ p, Y p ≅ L.X p := fun p =>
    Eq.mpr (congrArg (fun Z : C => Y p ≅ Z) (hLX p)) (B.totalRowHomologyIso p q)
  let f : ∀ p, Y (p + 1) ⟶ Y p := fun p => B.partialTotalHorizontalRowHomology p q
  have hpage : ∀ p, P₁.d (p + 1, q) (p, q) = (e (p + 1)).hom ≫ f p ≫ (e p).inv :=
    fun p => B.partialTotalSpectralSequenceFirstPage_d_eq p q
  have hrow : ∀ p, f p ≫ (r p).hom = (r (p + 1)).hom ≫ L.d (p + 1) p :=
    fun p => B.partialTotalHorizontalRowHomology_totalRowHomologyIso p q
  have hcomm : ∀ i j (_hij : (ComplexShape.down ℕ).Rel i j),
      (e i ≪≫ r i).hom ≫ L.d i j =
        (P₁.restriction (partialTotalFirstPageRowEmbedding q)).d i j ≫ (e j ≪≫ r j).hom := by
    exact partialTotalFirstPageCoordinateComm P₁ L q Y e r f hpage hrow
  exact HomologicalComplex.Hom.isoOfComponents
    (C₁ := P₁.restriction (partialTotalFirstPageRowEmbedding q)) (C₂ := L)
    (fun p => e p ≪≫ r p) hcomm

/-- Forward component of the signed first-page row comparison.

The degree-`p` forward component of the signed first-page row isomorphism is
`(B.partialTotalSpectralSequenceFirstPageRowIso p q).hom` followed by `(B.totalRowHomologyIso
p q).hom`. -/
@[simp]
theorem partialTotalFirstPageSignedVerticalHomologyIso_hom_f (p q : ℕ) :
    (B.partialTotalFirstPageSignedVerticalHomologyIso q).hom.f p =
      (B.partialTotalSpectralSequenceFirstPageRowIso p q).hom ≫
        (B.totalRowHomologyIso p q).hom := by
  rfl

/-- Inverse component of the signed first-page row comparison.

The degree-`p` inverse component of the signed first-page row isomorphism is
`(B.totalRowHomologyIso p q).inv` followed by `(B.partialTotalSpectralSequenceFirstPageRowIso
p q).inv`. -/
@[simp]
theorem partialTotalFirstPageSignedVerticalHomologyIso_inv_f (p q : ℕ) :
    (B.partialTotalFirstPageSignedVerticalHomologyIso q).inv.f p =
      (B.totalRowHomologyIso p q).inv ≫
        (B.partialTotalSpectralSequenceFirstPageRowIso p q).inv := by
  rfl

/-- First-page row as ordinary vertical homology.

At fixed vertical degree `q`, identify the restricted first page with signed vertical homology
and then remove the horizontal sign by `ε(q)^p` in degree `p`. The resulting complex
isomorphism has target `B.verticalHomologyComplex q`. -/
noncomputable def partialTotalFirstPageVerticalHomologyIso (q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).restriction
        (partialTotalFirstPageRowEmbedding q) ≅
      B.verticalHomologyComplex q :=
  B.partialTotalFirstPageSignedVerticalHomologyIso q ≪≫
    B.signedVerticalHomologyIso q

/-- Spectral interval coordinate for the second page.

For natural `p` and `q`, let the integer filtration cuts be `p - 2 ≤ p - 1 ≤ p ≤ p + 1`,
interpreted in `EInt`. With consecutive cochain degrees `-p-q-1`, `-p-q`, and `-p-q+1`, the
spectral object's `E` construction on these three arrows is the second-page coordinate. -/
noncomputable def partialTotalSpectralSequencePageTwoCoordinate
    (p q : ℕ) : C := by
  let Y := B.partialTotalSpectralObject
  let i₀ : EInt := (((p : ℤ) - 2 : ℤ) : EInt)
  let i₁ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₂ : EInt := ((p : ℤ) : EInt)
  let i₃ : EInt := (((p : ℤ) + 1 : ℤ) : EInt)
  let n₀ : ℤ := -(p : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(p : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(p : ℤ) - (q : ℤ) + 1
  have hi₀₁ : i₀ ≤ i₁ := by
    dsimp only [i₀, i₁]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₁₂ : i₁ ≤ i₂ := by
    dsimp only [i₁, i₂]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₂₃ : i₂ ≤ i₃ := by
    dsimp only [i₂, i₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hn₁ : n₀ + 1 = n₁ := by omega
  have hn₂ : n₁ + 1 = n₂ := by omega
  exact Y.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃)
    n₀ n₁ n₂ hn₁ hn₂

/-- Second-page object as its four-cut spectral coordinate.

The second-page object at `(p, q)` is isomorphic to
`B.partialTotalSpectralSequencePageTwoCoordinate p q`, using cuts `p - 2`, `p - 1`, `p`, and
`p + 1` and middle cochain degree `-p - q`. -/
noncomputable def partialTotalSpectralSequencePageTwoIso (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page (2 : ℤ)).X
        (p, q) ≅
      B.partialTotalSpectralSequencePageTwoCoordinate p q := by
  let Y := B.partialTotalSpectralObject
  let r : ℤ := 2
  let pq : ℕ × ℕ := (p, q)
  let i₀ : EInt := (((p : ℤ) - 2 : ℤ) : EInt)
  let i₁ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₂ : EInt := ((p : ℤ) : EInt)
  let i₃ : EInt := (((p : ℤ) + 1 : ℤ) : EInt)
  let n₀ : ℤ := -(p : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(p : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(p : ℤ) - (q : ℤ) + 1
  have hr : (1 : ℤ) ≤ r := by omega
  have h₀ : i₀ = (core).i₀ r pq hr := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
  have h₁ : i₁ = (core).i₁ pq := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁]
  have h₂ : i₂ = (core).i₂ pq := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂]
  have h₃ : i₃ = (core).i₃ r pq hr := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
    dsimp only [i₃, r, pq]
    congr 1
    omega
  have hn : n₁ = (core).deg pq := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
  have hn₁ : n₀ + 1 = n₁ := by omega
  have hn₂ : n₁ + 1 = n₂ := by omega
  exact Y.spectralSequencePageXIso core r hr pq
    i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ hn
      (hn₁ := hn₁) (hn₂ := hn₂)

/-- First-page homology as the second-page interval coordinate.

The homology of the first page at `(p, q)` is isomorphic to the same four-cut spectral object
that defines `B.partialTotalSpectralSequencePageTwoCoordinate p q`. The isomorphism comes from
homology data for the transition from page one to page two. -/
noncomputable def partialTotalSpectralSequencePageOneHomologyCoordinateIso
    (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page (1 : ℤ)).homology
        (p, q) ≅
      B.partialTotalSpectralSequencePageTwoCoordinate p q := by
  let Y := B.partialTotalSpectralObject
  let E := Y.spectralSequence core
  let pq : ℕ × ℕ := (p, q)
  let c₁ := ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩
  let pqPrev : ℕ × ℕ := c₁.prev pq
  let pqNext : ℕ × ℕ := c₁.next pq
  have hpq : c₁.prev pq = pqPrev := rfl
  have hpq' : c₁.next pq = pqNext := rfl
  let r : ℤ := 1
  let r' : ℤ := 2
  have hrr' : r + 1 = r' := by
    dsimp only [r, r']
    omega
  have hr : (1 : ℤ) ≤ r := by
    dsimp only [r]
    omega
  have hr' : (1 : ℤ) ≤ r' := by
    dsimp only [r']
    omega
  let i₀' : EInt := (((p : ℤ) - 2 : ℤ) : EInt)
  let i₀ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₁ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₂ : EInt := ((p : ℤ) : EInt)
  let i₃ : EInt := ((p : ℤ) : EInt)
  let i₃' : EInt := (((p : ℤ) + 1 : ℤ) : EInt)
  let n₀ : ℤ := -(p : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(p : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(p : ℤ) - (q : ℤ) + 1
  have hi₀' : i₀' = (core).i₀ r' pq hr' := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
  have hi₀ : i₀ = (core).i₀ r pq hr := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
  have hi₁ : i₁ = (core).i₁ pq := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁]
  have hi₂ : i₂ = (core).i₂ pq := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂]
  have hi₃ : i₃ = (core).i₃ r pq hr := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
    dsimp only [i₃, r, pq]
    congr 1
    omega
  have hi₃' : i₃' = (core).i₃ r' pq hr' := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
    dsimp only [i₃', r', pq]
    congr 1
    omega
  have hn : n₁ = (core).deg pq := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := by
    dsimp only [n₁, n₂]
  let D :=
    Y.spectralSequenceHomologyData core
      r r' hrr' hr pqPrev pq pqNext hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃'
      hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'
      n₀ n₁ n₂ hn hn₁ hn₂
  exact
    (E.page r).homologyIsoSc' pqPrev pq pqNext hpq hpq' ≪≫
      D.left.homologyIso

/-- First-page homology identifies with the second-page object.

For natural `p` and `q`, identify first-page homology at `(p, q)` and the second-page object
there through their common spectral interval coordinate. This gives `H(E¹)_(p,q) ≅ E²_(p,q)`. -/
noncomputable def partialTotalSpectralSequencePageOneTwoIso (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).homology
        (p, q) ≅
      ((B.partialTotalSpectralObject.spectralSequence core).page 2).X
        (p, q) :=
  B.partialTotalSpectralSequencePageOneHomologyCoordinateIso p q ≪≫
    (B.partialTotalSpectralSequencePageTwoIso p q).symm

/-- Zero-column page transition respects the common interval coordinate.

At `(0, q)`, the first-page-to-second-page isomorphism followed by the second-page interval
coordinate equals the first-page homology coordinate into that same interval object. -/
theorem
    partialTotalSpectralSequencePageOneTwoIso_zero_hom_comp_pageTwoIso_hom
    (q : ℕ) :
    (B.partialTotalSpectralSequencePageOneTwoIso 0 q).hom ≫
        (B.partialTotalSpectralSequencePageTwoIso 0 q).hom =
      (B.partialTotalSpectralSequencePageOneHomologyCoordinateIso 0 q).hom := by
  change
    ((B.partialTotalSpectralSequencePageOneHomologyCoordinateIso 0 q).hom ≫
        (B.partialTotalSpectralSequencePageTwoIso 0 q).inv) ≫
          (B.partialTotalSpectralSequencePageTwoIso 0 q).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Second page as horizontal homology of vertical homology.

For natural `p` and `q`, `E²_(p,q)` is isomorphic to `H_p(B.verticalHomologyComplex q)`. The
isomorphism passes through first-page homology, restricts to fixed vertical degree `q`, and
applies the complex isomorphism that removes the first-page horizontal sign. -/
noncomputable def partialTotalSecondPageVerticalHomologyIso (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 2).X
        (p, q) ≅
      (B.verticalHomologyComplex q).homology p :=
  (B.partialTotalSpectralSequencePageOneTwoIso p q).symm ≪≫
    (B.partialTotalFirstPageRowRestrictionHomologyIso p q).symm ≪≫
    HomologicalComplex.homologyMapIso
      (B.partialTotalFirstPageVerticalHomologyIso q) p

/-- Factorization of the second-page iterated-homology coordinate.

The forward map from `E²_(p,q)` to `H_p(B.verticalHomologyComplex q)` is the inverse page
transition, followed by the inverse fixed-row restriction homology coordinate, followed by the
homology map of `B.partialTotalFirstPageVerticalHomologyIso q`. -/
@[reassoc]
theorem partialTotalSecondPageVerticalHomologyIso_hom (p q : ℕ) :
    (B.partialTotalSecondPageVerticalHomologyIso p q).hom =
      (B.partialTotalSpectralSequencePageOneTwoIso p q).inv ≫
        (B.partialTotalFirstPageRowRestrictionHomologyIso p q).inv ≫
        HomologicalComplex.homologyMap
          (B.partialTotalFirstPageVerticalHomologyIso q).hom p :=
  rfl

/-- Lower-bound data for the first two spectral pages.

For a first-quadrant bicomplex `B`, this proposition records the integer bound `1 ≤ 1` used to
define its first page. The bound for page two and the transition equality `1 + 1 = 2` are
derived from this data. -/
structure PartialTotalFirstPageChoice
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) : Prop where
/-- Integer lower bound for page one.

The first-page choice contains the inequality `(1 : ℤ) ≤ 1`, which supplies the lower bound in
the spectral-sequence page construction. -/
  pageOneBound : (1 : ℤ) ≤ 1

/-- Canonical lower-bound data for page one.

Every first-quadrant bicomplex has a first-page choice, since `(1 : ℤ) ≤ 1`. -/
theorem partialTotalFirstPageChoice :
    PartialTotalFirstPageChoice B :=
  { pageOneBound := by omega }

namespace PartialTotalFirstPageChoice

variable {B}

/-- Successor equality for the first two pages.

For a first-page choice `χ`, the page indices satisfy `(1 : ℤ) + 1 = 2`. This equality is used
in the homology data for the transition. -/
theorem pageOneToTwo (χ : PartialTotalFirstPageChoice B) :
    (1 : ℤ) + 1 = 2 := by
  have hχ := χ.pageOneBound
  omega

/-- Integer lower bound for page two.

The first-page lower-bound data gives `(1 : ℤ) ≤ 2`, the bound used to define the second page. -/
theorem pageTwoBound (χ : PartialTotalFirstPageChoice B) : (1 : ℤ) ≤ 2 :=
  χ.pageOneBound.trans (by omega)

/-- First page with differential of bidegree minus one zero.

For a first-page choice `χ`, this is the page-one complex of the partial-total spectral
sequence, with shape `(-1, 0)` and lower bound `χ.pageOneBound`. -/
noncomputable abbrev pageOne (χ : PartialTotalFirstPageChoice B) :
    HomologicalComplex C
      (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩) :=
  (B.partialTotalSpectralObject.spectralSequence core).page
    1 χ.pageOneBound

/-- Second page with differential of bidegree minus two one.

For a first-page choice `χ`, this is the page-two complex of the partial-total spectral
sequence, with shape `(-2, 1)` and lower bound `χ.pageTwoBound`. -/
noncomputable abbrev pageTwo (χ : PartialTotalFirstPageChoice B) :
    HomologicalComplex C
      (ComplexShape.spectralSequenceNat ⟨(-2 : ℤ), 1⟩) :=
  (B.partialTotalSpectralObject.spectralSequence core).page
    2 χ.pageTwoBound

/-- Horizontal chain complex at fixed first-page vertical degree.

Restrict `χ.pageOne` along the embedding `p ↦ (p, q)`. This gives a natural-index chain
complex containing the first-page objects and horizontal differentials at vertical degree `q`. -/
noncomputable abbrev rowRestriction
    (χ : PartialTotalFirstPageChoice B) (q : ℕ) : ChainComplex C ℕ :=
  χ.pageOne.restriction (partialTotalFirstPageRowEmbedding q)

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- First-page core coordinate with a specified lower cut.

Let `k = core.i₁ (p, q)` and let `n₀ + 1 = core.deg (p, q)` and `core.deg (p, q) + 1 = n₂`.
These indices give an isomorphism from `χ.pageOne.X (p, q)` to the spectral homology of `k ⟶
core.i₂ (p, q)` in the core degree. -/
noncomputable def firstPageCoreIsoAtOfCut
    (χ : PartialTotalFirstPageChoice B)
    (p q : ℕ) (k : EInt)
    (hk : k = (core).i₁ (p, q))
    (n₀ n₂ : ℤ)
    (hn₀ : n₀ + 1 = (core).deg (p, q))
    (hn₂ : (core).deg (p, q) + 1 = n₂) :
    χ.pageOne.X (p, q) ≅
      (B.partialTotalSpectralObject.H ((core).deg (p, q))).obj
        (ComposableArrows.mk₁
          (homOfLE ((core).le₁₂' (p, q) hk rfl))) :=
  let Y := B.partialTotalSpectralObject
  CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      Y core 1 χ.pageOneBound (p, q)
      k k ((core).i₂ (p, q)) ((core).i₂ (p, q))
      (by rw [hk, ← (core).hi₀₁]) hk rfl
      (by rw [(core).hi₂₃])
      n₀ ((core).deg (p, q)) n₂ rfl hn₀ hn₂ ≪≫
    Y.EIsoH
      (homOfLE ((core).le₁₂' (p, q) hk rfl))
      n₀ ((core).deg (p, q)) n₂ hn₀ hn₂

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- Specified-cut core coordinate factors through spectral homology.

With the lower cut and neighboring cochain degrees specified, `χ.firstPageCoreIsoAtOfCut` is
the page interval-coordinate isomorphism followed by the spectral object's `EIsoH` for the
coincident outer and middle cuts on page one. -/
theorem firstPageCoreIsoAtOfCut_eq
    (χ : PartialTotalFirstPageChoice B)
    (p q : ℕ) (k : EInt)
    (hk : k = (core).i₁ (p, q))
    (n₀ n₂ : ℤ)
    (hn₀ : n₀ + 1 = (core).deg (p, q))
    (hn₂ : (core).deg (p, q) + 1 = n₂) :
    let Y := B.partialTotalSpectralObject
    χ.firstPageCoreIsoAtOfCut p q k hk n₀ n₂ hn₀ hn₂ =
      (CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
          Y core 1 χ.pageOneBound (p, q)
          k k ((core).i₂ (p, q)) ((core).i₂ (p, q))
          (by rw [hk, ← (core).hi₀₁]) hk rfl
          (by rw [(core).hi₂₃])
          n₀ ((core).deg (p, q)) n₂ rfl hn₀ hn₂ ≪≫
        Y.EIsoH
          (homOfLE ((core).le₁₂' (p, q) hk rfl))
          n₀ ((core).deg (p, q)) n₂ hn₀ hn₂) :=
  rfl

/-- First-page coordinate in its adjacent core interval.

For natural `p` and `q`, the first-page object `χ.pageOne.X (p, q)` is isomorphic to spectral
homology of `core.i₁ (p, q) ⟶ core.i₂ (p, q)` in degree `core.deg (p, q) = -p - q`. The
neighboring degrees are chosen as this degree minus and plus one. -/
noncomputable def firstPageCoreIsoAt
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageOne.X (p, q) ≅
      (B.partialTotalSpectralObject.H ((core).deg (p, q))).obj
        (ComposableArrows.mk₁ (homOfLE ((core).le₁₂ (p, q)))) :=
  χ.firstPageCoreIsoAtOfCut p q
    ((core).i₁ (p, q)) rfl
    ((core).deg (p, q) - 1)
    ((core).deg (p, q) + 1)
    (by omega) rfl

/-- Chosen first-page object in a specified total-row homology degree.

For `p + q = n`, the first-page object `χ.pageOne.X (p, q)` is isomorphic to `H_n(B.totalRow
p)`. This is the core interval-coordinate isomorphism followed by the partial-total step and
signed-row homology isomorphisms. -/
noncomputable def firstPageRowIsoAt
    (χ : PartialTotalFirstPageChoice B)
    (p q n : ℕ) (h : p + q = n) :
    χ.pageOne.X (p, q) ≅ (B.totalRow p).homology n :=
  χ.firstPageCoreIsoAt p q ≪≫
    B.partialTotalSpectralObjectHStepIso p q ≪≫
    B.partialTotalStepE₁HomologyIsoAt p q n h

/-- Neighbor identities for restriction of the first page.

At `(p, q)`, this proposition records the equality of the restricted middle index with `(p,
q)` and the compatibility of predecessor and successor indices under the row embedding. These
identities determine restriction coordinates for objects, cycles, and homology. -/
structure RestrictionIndex
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) : Prop where
/-- Middle-index identity for first-page row restriction.

For natural `p` and `q`, the row embedding in vertical degree `q` sends `p` to `(p, q)`. -/
  hMid : (partialTotalFirstPageRowEmbedding q).f p = (p, q)
/-- Incoming-neighbor identity for first-page row restriction.

The predecessor of `(p, q)` in the first-page shape `(-1, 0)` equals the row embedding of the
predecessor of `p` in the natural homological chain shape. Both represent the incoming
horizontal degree `p + 1`. -/
  hPrev :
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).prev (p, q) =
      (partialTotalFirstPageRowEmbedding q).f
        ((ComplexShape.down ℕ).prev p)
/-- Outgoing-neighbor identity for first-page row restriction.

The successor of `(p, q)` in the first-page shape `(-1, 0)` equals the row embedding of the
successor of `p` in the natural homological chain shape. At `p = 0`, both successor indices
stay at the same index because there is no outgoing horizontal arrow. -/
  hNext :
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).next (p, q) =
      (partialTotalFirstPageRowEmbedding q).f
        ((ComplexShape.down ℕ).next p)

/-- Canonical neighbor identities for first-page row restriction.

The fixed-row embedding satisfies the middle, predecessor, and successor identities at every
natural bidegree `(p, q)`. These give `χ.RestrictionIndex p q`. -/
theorem restrictionIndex
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.RestrictionIndex p q := by
  refine ⟨partialTotalFirstPageRowEmbedding_f p q, ?_, ?_⟩
  · apply (ComplexShape.spectralSequenceNat
      ⟨(-1 : ℤ), 0⟩).prev_eq'
    exact (partialTotalFirstPageRowEmbedding q).rel (by
      change p + 1 = (ComplexShape.down ℕ).prev p
      simp)
  · rcases p with _ | p
    · simp only [ChainComplex.next_nat_zero]
      apply (ComplexShape.spectralSequenceNat
        ⟨(-1 : ℤ), 0⟩).next_eq_self'
      intro z hz
      have hfst : (0 : ℤ) + (-1 : ℤ) = z.1 :=
        ((ComplexShape.spectralSequenceNat_rel_iff
          ⟨(-1 : ℤ), 0⟩ (0, q) z).mp hz).1
      omega
    · exact (ComplexShape.spectralSequenceNat
        ⟨(-1 : ℤ), 0⟩).next_eq'
          ((partialTotalFirstPageRowEmbedding q).rel (by
            simp only [ChainComplex.next_nat_succ]
            rfl))

/-- Object coordinate of the chosen first-page row restriction.

For restriction-index data `ρ` at `(p, q)`, the degree-`p` object of `χ.rowRestriction q` is
isomorphic to `χ.pageOne.X (p, q)`, using the middle-index equality. -/
noncomputable def restrictionXIso
    (χ : PartialTotalFirstPageChoice B) {p q : ℕ}
    (ρ : χ.RestrictionIndex p q) :
    (χ.rowRestriction q).X p ≅ χ.pageOne.X (p, q) :=
  χ.pageOne.restrictionXIso
    (partialTotalFirstPageRowEmbedding q) ρ.hMid

/-- Cycles coordinate of the chosen first-page row restriction.

For restriction-index data `ρ` at `(p, q)`, the degree-`p` cycles of `χ.rowRestriction q` are
isomorphic to the first-page cycles at `(p, q)`, using the successor-index equality. -/
noncomputable def restrictionCyclesIso
    (χ : PartialTotalFirstPageChoice B) {p q : ℕ}
    (ρ : χ.RestrictionIndex p q) :
    (χ.rowRestriction q).cycles p ≅ χ.pageOne.cycles (p, q) :=
  χ.pageOne.restrictionCyclesIsoAt
    (partialTotalFirstPageRowEmbedding q) p ρ.hNext

/-- Homology coordinate of the chosen first-page row restriction.

For restriction-index data `ρ` at `(p, q)`, `H_p(χ.rowRestriction q)` is isomorphic to
`χ.pageOne.homology (p, q)`. The coordinate uses both neighboring-index identities. -/
noncomputable def restrictionHomologyIso
    (χ : PartialTotalFirstPageChoice B) {p q : ℕ}
    (ρ : χ.RestrictionIndex p q) :
    (χ.rowRestriction q).homology p ≅
      χ.pageOne.homology (p, q) :=
  χ.pageOne.restrictionHomologyIsoAt
    (partialTotalFirstPageRowEmbedding q) p ρ.hPrev ρ.hNext

/-- Chosen restriction cycles coordinate respects cycle inclusion.

The forward cycles coordinate followed by the first-page cycle inclusion equals the row-
restriction cycle inclusion followed by its object coordinate at `(p, q)`. -/
@[reassoc]
theorem restrictionCyclesIso_hom_iCycles
    (χ : PartialTotalFirstPageChoice B) {p q : ℕ}
    (ρ : χ.RestrictionIndex p q) :
    (χ.restrictionCyclesIso ρ).hom ≫
        χ.pageOne.iCycles (p, q) =
      (χ.rowRestriction q).iCycles p ≫
        (χ.restrictionXIso ρ).hom := by
  exact HomologicalComplex.restrictionCyclesIsoAt_hom_iCycles
    χ.pageOne (partialTotalFirstPageRowEmbedding q) p ρ.hNext

/-- Chosen restriction homology coordinate respects projection from cycles.

Project the cycles of `χ.rowRestriction q` to its degree-`p` homology and apply the
restriction homology coordinate. This equals the cycles coordinate followed by the first-page
projection to homology at `(p, q)`. -/
@[reassoc]
theorem homologyπ_restrictionHomologyIso_hom
    (χ : PartialTotalFirstPageChoice B) {p q : ℕ}
    (ρ : χ.RestrictionIndex p q) :
    (χ.rowRestriction q).homologyπ p ≫
        (χ.restrictionHomologyIso ρ).hom =
      (χ.restrictionCyclesIso ρ).hom ≫
        χ.pageOne.homologyπ (p, q) := by
  exact HomologicalComplex.homologyπ_restrictionHomologyIsoAt_hom
    χ.pageOne (partialTotalFirstPageRowEmbedding q) p ρ.hPrev ρ.hNext

/-- Chosen first-page row term as vertical homology.

For natural `q` and `p`, the degree-`p` object of `χ.rowRestriction q` is isomorphic to
`H_q(B.X p)`. The isomorphism combines the restriction object coordinate, the first-page row
homology coordinate in total degree `q + p`, and the signed-row homology comparison. -/
noncomputable def componentIso
    (χ : PartialTotalFirstPageChoice B) (q p : ℕ) :
    (χ.rowRestriction q).X p ≅ (B.X p).homology q :=
  χ.restrictionXIso (χ.restrictionIndex p q) ≪≫
    χ.firstPageRowIsoAt p q (q + p) (Nat.add_comm p q) ≪≫
    B.totalRowHomologyIsoAt p q (q + p) (Nat.add_comm p q)

/- Compatibility of the fixed-row comparison with differentials -/

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- Chosen first-page row components respect the signed horizontal differential.

For a horizontal chain-shape arrow `i ⟶ j`, the component at `i` followed by the differential
of `B.signedVerticalHomologyComplex q` equals the row-restriction differential followed by the
component at `j`. The target differential contains the factor `ε(q)`. -/
theorem component_comm
    (χ : PartialTotalFirstPageChoice B)
    (q i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (χ.componentIso q i).hom ≫
        (B.signedVerticalHomologyComplex q).d i j =
      (χ.rowRestriction q).d i j ≫
        (χ.componentIso q j).hom := by
  change j + 1 = i at hij
  subst i
  let Y := B.partialTotalSpectralObject
  let P₁ := χ.pageOne
  let K := χ.rowRestriction q
  let m := j
  let NZero := q + m
  let NPlus := NZero + 1
  have hPlus : (m + 1) + q = NPlus := by
    dsimp only [NPlus, NZero, m]
    omega
  have hZero : m + q = NZero := Nat.add_comm m q
  let ePagePlus := χ.firstPageRowIsoAt (m + 1) q NPlus hPlus
  let ePageZero := χ.firstPageRowIsoAt m q NZero hZero
  let eRowPlus :
      (B.totalRow (m + 1)).homology NPlus ≅
        (B.signedVerticalHomologyComplex q).X (m + 1) :=
    B.totalRowHomologyIsoAt (m + 1) q NPlus hPlus
  let eRowZero :
      (B.totalRow m).homology NZero ≅
        (B.signedVerticalHomologyComplex q).X m :=
    B.totalRowHomologyIsoAt m q NZero hZero
  let dAt :
      (B.totalRow (m + 1)).homology NPlus ⟶
        (B.totalRow m).homology NZero :=
    ePagePlus.inv ≫ P₁.d (m + 1, q) (m, q) ≫ ePageZero.hom
  let eNat := ComplexShape.embeddingDownNat
  let νPlus : ℤ := -((NPlus : ℕ) : ℤ)
  let νZero : ℤ := -((NZero : ℕ) : ℤ)
  let S := B.partialTotalStepCochainShortComplex (m + 1)
  let T := B.partialTotalStepCochainShortComplex m
  let hS : S.ShortExact :=
    B.partialTotalStepCochainShortExact (m + 1)
  have hν : νPlus + 1 = νZero := by
    change -((NPlus : ℕ) : ℤ) + 1 = -((NZero : ℕ) : ℤ)
    omega
  let cAt :
      (B.totalRow (m + 1)).homology NPlus ⟶
        (B.totalRow m).homology NZero :=
    ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
      (HomologicalComplex.homologyMapIso
        (B.partialTotalStepCochainX₃Iso (m + 1)) νPlus).inv ≫
      hS.δ νPlus νZero hν ≫
      (HomologicalComplex.homologyMapIso
        (B.partialTotalAdjacentStepCochainIso m) νZero).hom ≫
      HomologicalComplex.homologyMap T.g νZero ≫
      (HomologicalComplex.homologyMapIso
        (B.partialTotalStepCochainX₃Iso m) νZero).hom ≫
      ((B.totalRow m).extendHomologyIso eNat rfl).hom
  let rAtNat :
      (B.totalRow (m + 1)).homology NPlus ⟶
        (B.totalRow m).homology NZero :=
    ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
      (HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) 0).shiftMap
          (B.partialTotalHorizontalRowShift m) νPlus νZero (by
            change 1 + -((NPlus : ℕ) : ℤ) = -((NZero : ℕ) : ℤ)
            omega) ≫
      ((B.totalRow m).extendHomologyIso eNat rfl).hom
  let rAt :
      (B.totalRow (m + 1)).homology NPlus ⟶
        (B.totalRow m).homology NZero :=
    ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
      (HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) 0).shiftMap
          (B.partialTotalHorizontalRowShift m)
          (eNat.f NPlus) (eNat.f NZero) (by
            change 1 + -((NPlus : ℕ) : ℤ) = -((NZero : ℕ) : ℤ)
            omega) ≫
      ((B.totalRow m).extendHomologyIso eNat rfl).hom
  let n : ℤ := (core).deg (m + 1, q)
  let n' : ℤ := (core).deg (m, q)
  have hnn' : n + 1 = n' := by
    dsimp only [n, n',
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
    omega
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  let fLeft := homOfLE ((core).le₁₂ (m, q))
  let fRight := homOfLE ((core).le₁₂' (m + 1, q) hmid rfl)
  have hPrev : (n - 1) + 1 = n := by omega
  have hNext : n' + 1 = n' + 1 := rfl
  let ePageSource := χ.firstPageCoreIsoAt (m + 1) q
  let ePageSourceCore := χ.firstPageCoreIsoAtOfCut
    (m + 1) q ((core).i₂ (m, q)) hmid
    (n - 1) n' hPrev hnn'
  let ePageSourceCoreX :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      Y core 1 χ.pageOneBound (m + 1, q)
      ((core).i₂ (m, q)) ((core).i₂ (m, q))
      ((core).i₂ (m + 1, q)) ((core).i₂ (m + 1, q))
      (by rw [hmid, ← (core).hi₀₁]) hmid rfl
      (by rw [(core).hi₂₃])
      (n - 1) n n' rfl hPrev hnn'
  let ePageSourceCoreH := Y.EIsoH fRight (n - 1) n n' hPrev hnn'
  have hSourceFactors :
      ePageSourceCore.hom =
        ePageSourceCoreX.hom ≫ ePageSourceCoreH.hom := by
    have h := congrArg Iso.hom
      (χ.firstPageCoreIsoAtOfCut_eq
        (m + 1) q ((core).i₂ (m, q)) hmid
        (n - 1) n' hPrev hnn')
    change ePageSourceCore.hom =
      ePageSourceCoreX.hom ≫ ePageSourceCoreH.hom at h
    exact h
  let γIdx :
      ComposableArrows.mk₁
          (homOfLE (show (core).i₂ (m, q) ≤ (core).i₂ (m + 1, q) by
            change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
            simp)) ≅
        ComposableArrows.mk₁
          (homOfLE ((core).le₁₂ (m + 1, q))) :=
    ComposableArrows.isoMk₁ (eqToIso hmid) (Iso.refl _)
  have hPageSource :
      ePageSource.inv ≫ ePageSourceCore.hom =
        (Y.H n).map γIdx.inv := by
    have hAux
        (k : EInt) (hk : k = (core).i₁ (m + 1, q))
        (n₂ : ℤ) (hn₂ : n + 1 = n₂) :
        let fK := homOfLE ((core).le₁₂' (m + 1, q) hk rfl)
        let γk :
            ComposableArrows.mk₁ fK ≅
              ComposableArrows.mk₁
                (homOfLE ((core).le₁₂ (m + 1, q))) :=
          ComposableArrows.isoMk₁ (eqToIso hk) (Iso.refl _)
        let ePageK := χ.firstPageCoreIsoAtOfCut
          (m + 1) q k hk (n - 1) n₂ hPrev hn₂
        ePageSource.inv ≫ ePageK.hom = (Y.H n).map γk.inv := by
      dsimp only
      subst k
      subst n₂
      dsimp only [ePageSource, firstPageCoreIsoAt]
      rw [Iso.inv_hom_id]
      rw [← (Y.H n).map_id]
      apply (Y.H n).congr_map
      subsingleton
    let γMid :
        ComposableArrows.mk₁
            (homOfLE ((core).le₁₂' (m + 1, q) hmid rfl)) ≅
          ComposableArrows.mk₁
            (homOfLE ((core).le₁₂ (m + 1, q))) :=
      ComposableArrows.isoMk₁ (eqToIso hmid) (Iso.refl _)
        (by subsingleton)
    calc
      _ = (Y.H n).map γMid.inv := by
        exact hAux ((core).i₂ (m, q)) hmid n' hnn'
      _ = (Y.H n).map γIdx.inv := by
        apply (Y.H n).congr_map
        apply ComposableArrows.hom_ext₁ <;> subsingleton
  let ePageTargetRaw := χ.firstPageCoreIsoAtOfCut
    m q ((core).i₁ (m, q)) rfl n (n' + 1) hnn' hNext
  let ePageTargetRawX :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      Y core 1 χ.pageOneBound (m, q)
      ((core).i₁ (m, q)) ((core).i₁ (m, q))
      ((core).i₂ (m, q)) ((core).i₂ (m, q))
      (by rw [← (core).hi₀₁]) rfl rfl
      (by rw [(core).hi₂₃])
      n n' (n' + 1) rfl hnn' hNext
  let ePageTargetRawH := Y.EIsoH fLeft n n' (n' + 1) hnn' hNext
  have hTargetFactors :
      ePageTargetRaw.inv =
        ePageTargetRawH.inv ≫ ePageTargetRawX.inv := by
    have h := congrArg Iso.inv
      (χ.firstPageCoreIsoAtOfCut_eq
        m q ((core).i₁ (m, q)) rfl
        n (n' + 1) hnn' hNext)
    change ePageTargetRaw.inv =
      ePageTargetRawH.inv ≫ ePageTargetRawX.inv at h
    exact h
  let ePageTarget := χ.firstPageCoreIsoAt m q
  have hPageTarget :
      ePageTargetRaw.inv ≫ ePageTarget.hom = 𝟙 _ := by
    have hTargetCoordinate
        (n₀ : ℤ) (hn₀ : n₀ + 1 = n') :
        χ.firstPageCoreIsoAtOfCut
            m q ((core).i₁ (m, q)) rfl
            n₀ (n' + 1) hn₀ hNext =
          ePageTarget := by
      have h : n₀ = n' - 1 := by omega
      subst n₀
      dsimp only [ePageTarget, firstPageCoreIsoAt]
    have hTargetIso : ePageTargetRaw = ePageTarget :=
      hTargetCoordinate n hnn'
    have hInv : ePageTargetRaw.inv = ePageTarget.inv :=
      congrArg Iso.inv hTargetIso
    calc
      ePageTargetRaw.inv ≫ ePageTarget.hom =
          ePageTarget.inv ≫ ePageTarget.hom :=
        congrArg (fun f => f ≫ ePageTarget.hom) hInv
      _ = 𝟙 _ := ePageTarget.inv_hom_id
  let dRaw := Y.d (𝟙 _) fLeft (𝟙 _) fRight (𝟙 _)
    (n - 1) n n' (n' + 1) hPrev hnn' hNext
  have hpageRaw :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq
      Y core 1 χ.pageOneBound (m + 1, q) (m, q)
      (coreE₁IncreasingHomologicalNat_rel_succ m q)
      (𝟙 _) fLeft (𝟙 _) fRight (𝟙 _)
      (by rw [← (core).hi₀₁]) rfl
      (by rw [hmid, ← (core).hi₀₁]) hmid rfl
      (by rw [(core).hi₂₃])
      (n - 1) n n' (n' + 1) rfl hPrev hnn' hNext
  change P₁.d (m + 1, q) (m, q) =
    ePageSourceCoreX.hom ≫ dRaw ≫ ePageTargetRawX.inv at hpageRaw
  have hD :
      dRaw = ePageSourceCoreH.hom ≫
        Y.δ fLeft fRight n n' hnn' ≫ ePageTargetRawH.inv := by
    apply (cancel_mono ePageTargetRawH.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Y.d_EIsoH_hom fLeft fRight
      (n - 1) n n' (n' + 1) hPrev hnn' hNext
  have hpage :
      P₁.d (m + 1, q) (m, q) =
        ePageSourceCore.hom ≫ Y.δ fLeft fRight n n' hnn' ≫
          ePageTargetRaw.inv := by
    rw [hpageRaw, hD]
    rw [hSourceFactors, hTargetFactors]
    simp only [Category.assoc]
    exact (Category.assoc
      ePageSourceCoreX.hom ePageSourceCoreH.hom
      (Y.δ fLeft fRight n n' hnn' ≫
        ePageTargetRawH.inv ≫ ePageTargetRawX.inv)).symm
  have hPagePresented :
      ePageSource.inv ≫ P₁.d (m + 1, q) (m, q) ≫ ePageTarget.hom =
        (Y.H n).map γIdx.inv ≫
          Y.δ fLeft fRight n n' hnn' := by
    have hpageAt :=
      congrArg
        (fun (k : P₁.X (m + 1, q) ⟶ P₁.X (m, q)) =>
          ePageSource.inv ≫ k ≫ ePageTarget.hom)
        hpage
    have hSourceAt :
        ((ePageSource.inv ≫ ePageSourceCore.hom) ≫
              Y.δ fLeft fRight n n' hnn') ≫
            (ePageTargetRaw.inv ≫ ePageTarget.hom) =
          (((Y.H n).map γIdx.inv ≫
              Y.δ fLeft fRight n n' hnn') ≫
            (ePageTargetRaw.inv ≫ ePageTarget.hom)) :=
      congrArg
        (fun f =>
          (f ≫ Y.δ fLeft fRight n n' hnn') ≫
            (ePageTargetRaw.inv ≫ ePageTarget.hom))
        hPageSource
    have hTargetAt :
        (((Y.H n).map γIdx.inv ≫
              Y.δ fLeft fRight n n' hnn') ≫
            (ePageTargetRaw.inv ≫ ePageTarget.hom)) =
          (((Y.H n).map γIdx.inv ≫
              Y.δ fLeft fRight n n' hnn') ≫ 𝟙 _) :=
      congrArg
        (fun f =>
          ((Y.H n).map γIdx.inv ≫
            Y.δ fLeft fRight n n' hnn') ≫ f)
        hPageTarget
    calc
      ePageSource.inv ≫ P₁.d (m + 1, q) (m, q) ≫ ePageTarget.hom =
          ePageSource.inv ≫
            (ePageSourceCore.hom ≫
              Y.δ fLeft fRight n n' hnn' ≫ ePageTargetRaw.inv) ≫
            ePageTarget.hom := hpageAt
      _ = (((ePageSource.inv ≫ ePageSourceCore.hom) ≫
              Y.δ fLeft fRight n n' hnn') ≫
            (ePageTargetRaw.inv ≫ ePageTarget.hom)) := by
          simp only [Category.assoc]
      _ = ((Y.H n).map γIdx.inv ≫
              Y.δ fLeft fRight n n' hnn') ≫
            (ePageTargetRaw.inv ≫ ePageTarget.hom) := hSourceAt
      _ = ((Y.H n).map γIdx.inv ≫
              Y.δ fLeft fRight n n' hnn') ≫ 𝟙 _ := hTargetAt
      _ = (Y.H n).map γIdx.inv ≫
            Y.δ fLeft fRight n n' hnn' := Category.comp_id _
  have hDeltaAt : dAt = cAt := by
    dsimp only [dAt, ePagePlus, ePageZero, firstPageRowIsoAt]
    simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
    slice_lhs 3 5 => rw [hPagePresented]
    slice_lhs 2 5 => erw [B.partialTotalE₁_delta_conjugation m q]
    erw [B.partialTotalE₁_mappingConeDifferential_eq_connectingAt
      m q NPlus NZero hPlus hZero hS hν hnn']
  have hConnectingAtNat : cAt = rAtNat := by
    simpa only [cAt, rAtNat, eNat, νPlus, νZero, S, T, hS,
      Category.assoc] using
      B.partialTotalE₁Connecting_eq_horizontalRowAt
        m q NPlus NZero hPlus hZero
  have hRAt : rAtNat = rAt := by
    let D := { d : ℤ × ℤ //
      eNat.f NPlus = d.1 ∧ eNat.f NZero = d.2 }
    let dNat : D := ⟨(νPlus, νZero), rfl, rfl⟩
    let dEmbed : D :=
      ⟨(eNat.f NPlus, eNat.f NZero), rfl, rfl⟩
    have hRel (d : D) : 1 + d.1.1 = d.1.2 := by
      rw [← d.2.1, ← d.2.2]
      change 1 + -((NPlus : ℕ) : ℤ) = -((NZero : ℕ) : ℤ)
      omega
    let wholeAt (d : D) :
        (B.totalRow (m + 1)).homology NPlus ⟶
          (B.totalRow m).homology NZero :=
      ((B.totalRow (m + 1)).extendHomologyIso eNat d.2.1).inv ≫
        (HomologicalComplex.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftMap
            (B.partialTotalHorizontalRowShift m)
              d.1.1 d.1.2 (hRel d) ≫
        ((B.totalRow m).extendHomologyIso eNat d.2.2).hom
    have hd : dNat = dEmbed := by
      apply Subtype.ext
      apply Prod.ext <;> rfl
    have hRAtNatWhole : rAtNat = wholeAt dNat := by
      dsimp only [rAtNat, wholeAt, dNat, D]
      rfl
    have hWholeRAt : wholeAt dEmbed = rAt := by
      dsimp only [rAt, wholeAt, dEmbed, D]
    exact hRAtNatWhole.trans
      ((congrArg wholeAt hd).trans hWholeRAt)
  have hConnectingAt : cAt = rAt :=
    hConnectingAtNat.trans hRAt
  have hRowAt :
      rAt ≫ eRowZero.hom =
        eRowPlus.hom ≫
          (B.signedVerticalHomologyComplex q).d (m + 1) m := by
    dsimp only [rAt, eNat, νPlus, νZero, eRowZero, eRowPlus,
      NPlus, NZero]
    erw [B.partialTotalHorizontalRowHomology_totalRowHomologyIsoAt
      m q hPlus hZero]
    rfl
  have hRowD :
      dAt ≫ eRowZero.hom =
        eRowPlus.hom ≫
          (B.signedVerticalHomologyComplex q).d (m + 1) m := by
    rw [hDeltaAt, hConnectingAt, hRowAt]
  have hBase :
      (ePagePlus.hom ≫ eRowPlus.hom) ≫
          (B.signedVerticalHomologyComplex q).d (m + 1) m =
        P₁.d (m + 1, q) (m, q) ≫
          (ePageZero.hom ≫ eRowZero.hom) := by
    simp only [Category.assoc]
    rw [← hRowD]
    dsimp only [dAt]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change
    (χ.componentIso q (m + 1)).hom ≫
        (B.signedVerticalHomologyComplex q).d (m + 1) m =
      K.d (m + 1) m ≫ (χ.componentIso q m).hom
  let ρPlus : χ.RestrictionIndex (m + 1) q :=
    χ.restrictionIndex (m + 1) q
  let ρZero : χ.RestrictionIndex m q :=
    χ.restrictionIndex m q
  let eXPlus : K.X (m + 1) ≅ P₁.X (m + 1, q) :=
    χ.restrictionXIso ρPlus
  let eXZero : K.X m ≅ P₁.X (m, q) :=
    χ.restrictionXIso ρZero
  have hRestriction :
      K.d (m + 1) m =
        eXPlus.hom ≫ P₁.d (m + 1, q) (m, q) ≫ eXZero.inv := by
    exact P₁.restriction_d_eq
      (partialTotalFirstPageRowEmbedding q) ρPlus.hMid ρZero.hMid
  have hPre := congrArg (fun f => eXPlus.hom ≫ f) hBase
  change
    (eXPlus.hom ≫ ePagePlus.hom ≫ eRowPlus.hom) ≫
        (B.signedVerticalHomologyComplex q).d (m + 1) m =
      K.d (m + 1) m ≫
        (eXZero.hom ≫ ePageZero.hom ≫ eRowZero.hom)
  rw [hRestriction]
  simp only [Category.assoc]
  slice_rhs 3 4 => rw [eXZero.inv_hom_id]
  simp only [Category.id_comp]
  simpa only [Category.assoc] using hPre

/- Comparison with ordinary vertical homology -/


/-- Chosen first-page row as the ordinary vertical-homology complex.

The component isomorphisms identify `χ.rowRestriction q` with signed vertical homology.
Composing with multiplication by `ε(q)^p` in horizontal degree `p` gives an isomorphism to
`B.verticalHomologyComplex q`. -/
noncomputable def verticalHomologyIso
    (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    χ.rowRestriction q ≅ B.verticalHomologyComplex q :=
  HomologicalComplex.Hom.isoOfComponents
      (fun p => χ.componentIso q p)
      (fun i j hij => χ.component_comm q i j hij) ≪≫
    B.signedVerticalHomologyIso q

/-- Chosen vertical-homology comparison has its component inverse at zero.

In horizontal degree zero, the inverse of `χ.verticalHomologyIso q` is `(χ.componentIso q
0).inv`. The sign-removal factor is `ε(q)^0 = 1`. -/
theorem verticalHomologyIso_inv_f_zero
    (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    (χ.verticalHomologyIso q).inv.f 0 =
      (χ.componentIso q 0).inv := by
  let K := χ.rowRestriction q
  let components : ∀ p, K.X p ≅
      (B.signedVerticalHomologyComplex q).X p :=
    fun p => χ.componentIso q p
  let hcomm : ∀ i j, (ComplexShape.down ℕ).Rel i j →
      (components i).hom ≫
          (B.signedVerticalHomologyComplex q).d i j =
        K.d i j ≫ (components j).hom :=
    fun i j hij => χ.component_comm q i j hij
  let eSigned : K ≅ B.signedVerticalHomologyComplex q :=
    HomologicalComplex.Hom.isoOfComponents components hcomm
  let eVertical : K ≅ B.verticalHomologyComplex q :=
    eSigned ≪≫ B.signedVerticalHomologyIso q
  change eVertical.inv.f 0 = _
  have hApp :=
    HomologicalComplex.Hom.isoOfComponents_app components hcomm 0
  have hSignedInv :
      eSigned.inv.f 0 = (χ.componentIso q 0).inv := by
    change (HomologicalComplex.Hom.isoApp eSigned 0).inv = _
    rw [hApp]
  change (B.signedVerticalHomologyIso q).inv.f 0 ≫
      eSigned.inv.f 0 = _
  rw [signedVerticalHomologyIso_inv_f, hSignedInv]
  simp only [pow_zero, inv_one, one_smul]
  exact Category.id_comp _

/- Page-one transition HomologyData -/


/-- Filtration cuts and degrees for the first-page homology transition.

At natural `(p, q)`, this data specifies the neighboring first-page bidegrees, six filtration
cuts for pages one and two, and three consecutive cochain degrees. The identities identify the
cuts with `p - 2`, `p - 1`, `p - 1`, `p`, `p`, and `p + 1`, and the middle degree with `-p -
q`, retaining integer indices at column zero. -/
structure PageTransitionIndex
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) : Type where
  /-- Incoming bidegree for the first-page transition.

A bidegree identified by `hpq` with the predecessor of `(p, q)` for the shape `(-1, 0)`,
namely the source of the incoming horizontal arrow. -/
  pqPrev : ℕ × ℕ
  /-- Outgoing bidegree for the first-page transition.

A bidegree identified by `hpq'` with the successor of `(p, q)` for the shape `(-1, 0)`. At
column zero this successor index stays at `(0, q)`. -/
  pqNext : ℕ × ℕ
/-- Incoming-index equality for the first-page transition.

The stored incoming bidegree equals `(ComplexShape.spectralSequenceNat ⟨-1, 0⟩).prev (p, q)`. -/
  hpq :
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).prev (p, q) = pqPrev
/-- Outgoing-index equality for the first-page transition.

The stored outgoing bidegree equals `(ComplexShape.spectralSequenceNat ⟨-1, 0⟩).next (p, q)`. -/
  hpq' :
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).next (p, q) = pqNext
  /-- Outer lower cut on page two.

The lower outer filtration cut, identified by `hi₀'` with `core.i₀ 2 (p, q)`. It is the
integer `p - 2`, interpreted in `EInt`. -/
  i₀' : EInt
  /-- Outer lower cut on page one.

The lower outer filtration cut, identified by `hi₀` with `core.i₀ 1 (p, q)`. It is the integer
`p - 1`, interpreted in `EInt`. -/
  i₀ : EInt
  /-- Lower middle cut shared by the first two pages.

The middle cut identified by `hi₁` with `core.i₁ (p, q)`, namely the integer `p - 1` in
`EInt`. -/
  i₁ : EInt
  /-- Upper middle cut shared by the first two pages.

The middle cut identified by `hi₂` with `core.i₂ (p, q)`, namely the integer `p` in `EInt`. -/
  i₂ : EInt
  /-- Outer upper cut on page one.

The upper outer filtration cut, identified by `hi₃` with `core.i₃ 1 (p, q)`, namely the
integer `p` in `EInt`. -/
  i₃ : EInt
  /-- Outer upper cut on page two.

The upper outer filtration cut, identified by `hi₃'` with `core.i₃ 2 (p, q)`, namely the
integer `p + 1` in `EInt`. -/
  i₃' : EInt
  /-- Lower neighboring cochain degree for the page transition.

The cochain degree satisfying `n₀ + 1 = n₁`. Since the middle degree is `-p - q`, this degree
is `-p - q - 1`. -/
  n₀ : ℤ
  /-- Middle cochain degree for the page transition.

The degree identified by `hn` with `core.deg (p, q)`, namely `-p - q`. -/
  n₁ : ℤ
  /-- Upper neighboring cochain degree for the page transition.

The cochain degree satisfying `n₁ + 1 = n₂`, hence `-p - q + 1`. -/
  n₂ : ℤ
/-- Identification of the page-two lower outer cut.

The cut `i₀'` equals `core.i₀ 2 (p, q) χ.pageTwoBound`, so it is the integer `p - 2` in
`EInt`. -/
  hi₀' : i₀' = (core).i₀ 2 (p, q) χ.pageTwoBound
/-- Identification of the page-one lower outer cut.

The cut `i₀` equals `core.i₀ 1 (p, q) χ.pageOneBound`, so it is the integer `p - 1` in `EInt`. -/
  hi₀ : i₀ = (core).i₀ 1 (p, q) χ.pageOneBound
/-- Identification of the lower middle cut.

The cut `i₁` equals `core.i₁ (p, q)`, which is the integer `p - 1` in `EInt`. -/
  hi₁ : i₁ = (core).i₁ (p, q)
/-- Identification of the upper middle cut.

The cut `i₂` equals `core.i₂ (p, q)`, which is the integer `p` in `EInt`. -/
  hi₂ : i₂ = (core).i₂ (p, q)
/-- Identification of the page-one upper outer cut.

The cut `i₃` equals `core.i₃ 1 (p, q) χ.pageOneBound`, which is the integer `p` in `EInt`. -/
  hi₃ : i₃ = (core).i₃ 1 (p, q) χ.pageOneBound
/-- Identification of the page-two upper outer cut.

The cut `i₃'` equals `core.i₃ 2 (p, q) χ.pageTwoBound`, which is the integer `p + 1` in
`EInt`. -/
  hi₃' : i₃' = (core).i₃ 2 (p, q) χ.pageTwoBound
/-- Identification of the page-transition middle degree.

The stored middle degree satisfies `n₁ = core.deg (p, q) = -p - q`. -/
  hn : n₁ = (core).deg (p, q)
/-- Consecutiveness of the lower and middle transition degrees.

The lower and middle cochain degrees satisfy `n₀ + 1 = n₁`. -/
  hn₁ : n₀ + 1 = n₁
/-- Consecutiveness of the middle and upper transition degrees.

The middle and upper cochain degrees satisfy `n₁ + 1 = n₂`. -/
  hn₂ : n₁ + 1 = n₂
/-- Bottom bound for the page-two lower outer cut.

The bottom extended-integer index satisfies `⊥ ≤ i₀'`. -/
  hiBot₀' : (⊥ : EInt) ≤ i₀'
/-- Page-two lower outer cut precedes the lower middle cut.

The page-transition cuts satisfy `i₀' ≤ i₁`, giving the interval from integer `p - 2` to `p -
1`. -/
  hi₀'₁ : i₀' ≤ i₁
/-- Lower outer cut expands from page one to page two.

The lower outer cuts satisfy `i₀' ≤ i₀`, comparing the page-two cut `p - 2` with the page-one
cut `p - 1`. -/
  hi₀'₀ : i₀' ≤ i₀
/-- Page-one lower outer cut precedes its middle cut.

The page-transition cuts satisfy `i₀ ≤ i₁`; both are identified with integer `p - 1`. -/
  hi₀₁ : i₀ ≤ i₁
/-- Ordering of the shared middle cuts.

The shared middle cuts satisfy `i₁ ≤ i₂`, giving the interval from integer `p - 1` to `p`. -/
  hi₁₂ : i₁ ≤ i₂
/-- Page-one upper middle cut precedes its outer cut.

The page-transition cuts satisfy `i₂ ≤ i₃`; both are identified with integer `p`. -/
  hi₂₃ : i₂ ≤ i₃
/-- Upper middle cut precedes the page-two outer cut.

The page-transition cuts satisfy `i₂ ≤ i₃'`, giving the interval from integer `p` to `p + 1`. -/
  hi₂₃' : i₂ ≤ i₃'
/-- Upper outer cut expands from page one to page two.

The upper outer cuts satisfy `i₃ ≤ i₃'`, comparing the page-one cut `p` with the page-two cut
`p + 1`. -/
  hi₃₃' : i₃ ≤ i₃'
/-- Bottom bound for the lower middle cut.

The bottom extended-integer index satisfies `⊥ ≤ i₁`. -/
  hiBot₁ : (⊥ : EInt) ≤ i₁
/-- Top bound for the page-two upper outer cut.

The page-two upper outer cut satisfies `i₃' ≤ ⊤`. -/
  hi₃'Top : i₃' ≤ (⊤ : EInt)

/-- Canonical integer cuts for the first-page transition.

For natural `p` and `q`, choose the neighboring bidegrees from the first-page shape, the six
cuts `p - 2`, `p - 1`, `p - 1`, `p`, `p`, `p + 1` in `EInt`, and degrees `-p - q - 1`, `-p -
q`, `-p - q + 1`. Their ordering and core identities give `χ.PageTransitionIndex p q`. -/
noncomputable def pageTransitionIndex
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.PageTransitionIndex p q := by
  let c₁ := ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩
  let pq : ℕ × ℕ := (p, q)
  let i₀' : EInt := (((p : ℤ) - 2 : ℤ) : EInt)
  let i₀ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₁ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₂ : EInt := ((p : ℤ) : EInt)
  let i₃ : EInt := ((p : ℤ) : EInt)
  let i₃' : EInt := (((p : ℤ) + 1 : ℤ) : EInt)
  let n₀ : ℤ := -(p : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(p : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(p : ℤ) - (q : ℤ) + 1
  refine
    { pqPrev := c₁.prev pq
      pqNext := c₁.next pq
      hpq := rfl
      hpq' := rfl
      i₀' := i₀'
      i₀ := i₀
      i₁ := i₁
      i₂ := i₂
      i₃ := i₃
      i₃' := i₃'
      n₀ := n₀
      n₁ := n₁
      n₂ := n₂
      hi₀' := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
      hi₀ := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
      hi₁ := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁]
      hi₂ := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂]
      hi₃ := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
        dsimp only [i₃, pq]
        congr 1
        omega
      hi₃' := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
        dsimp only [i₃', pq]
        congr 1
        omega
      hn := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
      hn₁ := by omega
      hn₂ := by omega
      hiBot₀' := bot_le
      hi₀'₁ := by
        dsimp only [i₀', i₁]
        simp only [WithBotTop.coe_le_coe]
        omega
      hi₀'₀ := by
        dsimp only [i₀', i₀]
        simp only [WithBotTop.coe_le_coe]
        omega
      hi₀₁ := by
        dsimp only [i₀, i₁]
        simp only [WithBotTop.coe_le_coe]
        rfl
      hi₁₂ := by
        dsimp only [i₁, i₂]
        simp only [WithBotTop.coe_le_coe]
        omega
      hi₂₃ := by
        dsimp only [i₂, i₃]
        simp only [WithBotTop.coe_le_coe]
        rfl
      hi₂₃' := by
        dsimp only [i₂, i₃']
        simp only [WithBotTop.coe_le_coe]
        omega
      hi₃₃' := by
        dsimp only [i₃, i₃']
        simp only [WithBotTop.coe_le_coe]
        omega
      hiBot₁ := bot_le
      hi₃'Top := le_top }

/-- Homology data for the chosen first-page differential.

Using the neighboring bidegrees and integer cuts in `χ.pageTransitionIndex p q`, the spectral
object supplies homology data for the short complex of first-page objects around `(p, q)`. Its
homology coordinate is shared with page two. -/
noncomputable def pageOneHomologyData
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    let η := χ.pageTransitionIndex p q
    (χ.pageOne.sc' η.pqPrev (p, q) η.pqNext).HomologyData := by
  let Y := B.partialTotalSpectralObject
  let η := χ.pageTransitionIndex p q
  exact Y.spectralSequenceHomologyData core
    1 2 χ.pageOneToTwo χ.pageOneBound
    η.pqPrev (p, q) η.pqNext η.hpq η.hpq'
    η.i₀' η.i₀ η.i₁ η.i₂ η.i₃ η.i₃'
    η.hi₀' η.hi₀ η.hi₁ η.hi₂ η.hi₃ η.hi₃'
    η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- Cycle inclusion in the chosen page-transition homology data.

For `η = χ.pageTransitionIndex p q`, the left inclusion in the homology data is the spectral
object's `mapFourδ₁Toδ₀'` on the lower five cuts, followed by the inverse page-one interval
coordinate. The three degrees are `η.n₀`, `η.n₁`, and `η.n₂`. -/
@[reassoc]
theorem pageOneHomologyData_left_i
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    let η := χ.pageTransitionIndex p q
    (χ.pageOneHomologyData p q).left.i =
      B.partialTotalSpectralObject.mapFourδ₁Toδ₀'
          η.i₀' η.i₀ η.i₁ η.i₂ η.i₃
          η.hi₀'₀ η.hi₀₁ η.hi₁₂ η.hi₂₃
          η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ ≫
        (CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
          B.partialTotalSpectralObject core 1 χ.pageOneBound (p, q)
          η.i₀ η.i₁ η.i₂ η.i₃
          η.hi₀ η.hi₁ η.hi₂ η.hi₃
          η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂).inv := by
  let Y := B.partialTotalSpectralObject
  let η := χ.pageTransitionIndex p q
  exact
    CategoryTheory.Abelian.SpectralObject.spectralSequenceHomologyData_left_i
      Y core 1 2 χ.pageOneToTwo χ.pageOneBound
      η.pqPrev (p, q) η.pqNext η.hpq η.hpq'
      η.i₀' η.i₀ η.i₁ η.i₂ η.i₃ η.i₃'
      η.hi₀' η.hi₀ η.hi₁ η.hi₂ η.hi₃ η.hi₃'
      η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- Homology projection in the chosen page-transition data.

For `η = χ.pageTransitionIndex p q`, the left projection in the homology data is the spectral
object's `mapFourδ₄Toδ₃'` on cuts `η.i₀'`, `η.i₁`, `η.i₂`, `η.i₃`, and `η.i₃'`, in the three
consecutive cochain degrees. -/
@[reassoc]
theorem pageOneHomologyData_left_π
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    let η := χ.pageTransitionIndex p q
    (χ.pageOneHomologyData p q).left.π =
      B.partialTotalSpectralObject.mapFourδ₄Toδ₃'
        η.i₀' η.i₁ η.i₂ η.i₃ η.i₃'
        η.hi₀'₁ η.hi₁₂ η.hi₂₃ η.hi₃₃'
        η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ := by
  let Y := B.partialTotalSpectralObject
  let η := χ.pageTransitionIndex p q
  exact
    CategoryTheory.Abelian.SpectralObject.spectralSequenceHomologyData_left_π
      Y core 1 2 χ.pageOneToTwo χ.pageOneBound
      η.pqPrev (p, q) η.pqNext η.hpq η.hpq'
      η.i₀' η.i₀ η.i₁ η.i₂ η.i₃ η.i₃'
      η.hi₀' η.hi₀ η.hi₁ η.hi₂ η.hi₃ η.hi₃'
      η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂

/- Common page-one and page-two coordinates -/


/-- Common homology object for the chosen first two pages.

For natural `p` and `q`, this is the homology object `(χ.pageOneHomologyData p q).left.H`. It
is the common coordinate for first-page homology and the second-page object at `(p, q)`. -/
noncomputable abbrev pageTwoCoordinate
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) : C :=
  (χ.pageOneHomologyData p q).left.H

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- Chosen second-page object as the common homology coordinate.

The second-page object `χ.pageTwo.X (p, q)` is isomorphic to `χ.pageTwoCoordinate p q`. Its
spectral interval uses the lower outer cut `i₀'`, middle cuts `i₁` and `i₂`, and upper outer
cut `i₃'` from the transition data. -/
noncomputable def pageTwoCoordinateIso
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageTwo.X (p, q) ≅ χ.pageTwoCoordinate p q := by
  let η := χ.pageTransitionIndex p q
  exact
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      B.partialTotalSpectralObject core 2 χ.pageTwoBound (p, q)
      η.i₀' η.i₁ η.i₂ η.i₃'
      η.hi₀' η.hi₁ η.hi₂ η.hi₃'
      η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- Four-cut second-page interval as the chosen homology coordinate.

With `η = χ.pageTransitionIndex p q`, the spectral object's `E` on intervals `η.i₀' ⟶ η.i₁ ⟶
η.i₂ ⟶ η.i₃'` and degrees `η.n₀`, `η.n₁`, `η.n₂` is isomorphic to `χ.pageTwoCoordinate p q`. -/
noncomputable def pageTwoRawCoordinateIso
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    let η := χ.pageTransitionIndex p q
    B.partialTotalSpectralObject.E
        (homOfLE η.hi₀'₁) (homOfLE η.hi₁₂) (homOfLE η.hi₂₃')
        η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ ≅
      χ.pageTwoCoordinate p q := by
  let η := χ.pageTransitionIndex p q
  let ePage₂ :
      χ.pageTwo.X (p, q) ≅
        B.partialTotalSpectralObject.E
          (homOfLE η.hi₀'₁) (homOfLE η.hi₁₂) (homOfLE η.hi₂₃')
          η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      B.partialTotalSpectralObject core 2 χ.pageTwoBound (p, q)
      η.i₀' η.i₁ η.i₂ η.i₃'
      η.hi₀' η.hi₁ η.hi₂ η.hi₃'
      η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂
  exact ePage₂.symm ≪≫ χ.pageTwoCoordinateIso p q

/-- Chosen first-page homology as the common coordinate.

The homology of `χ.pageOne` at `(p, q)` is isomorphic to `χ.pageTwoCoordinate p q`. First
identify it with homology of the neighboring short complex, then use the spectral-object
homology data. -/
noncomputable def pageOneHomologyCoordinateIso
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageOne.homology (p, q) ≅ χ.pageTwoCoordinate p q := by
  let η := χ.pageTransitionIndex p q
  exact
    χ.pageOne.homologyIsoSc'
        η.pqPrev (p, q) η.pqNext η.hpq η.hpq' ≪≫
      (χ.pageOneHomologyData p q).left.homologyIso

/-- Chosen first-page homology identifies with page two.

For natural `p` and `q`, the isomorphism `χ.pageOne.homology (p, q) ≅ χ.pageTwo.X (p, q)` is
obtained by composing the first-page homology coordinate with the inverse second-page
coordinate. -/
noncomputable def pageOneTwoIso
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageOne.homology (p, q) ≅ χ.pageTwo.X (p, q) :=
  χ.pageOneHomologyCoordinateIso p q ≪≫
    (χ.pageTwoCoordinateIso p q).symm

/-- Chosen zero-column transition respects its common homology object.

At `(0, q)`, the chosen first-page-to-second-page map followed by `χ.pageTwoCoordinateIso 0 q`
equals `χ.pageOneHomologyCoordinateIso 0 q` on forward morphisms. -/
@[reassoc]
theorem pageOneTwoIso_zero_hom_comp_pageTwoCoordinateIso_hom
    (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    (χ.pageOneTwoIso 0 q).hom ≫
        (χ.pageTwoCoordinateIso 0 q).hom =
      (χ.pageOneHomologyCoordinateIso 0 q).hom := by
  change
    ((χ.pageOneHomologyCoordinateIso 0 q).hom ≫
        (χ.pageTwoCoordinateIso 0 q).inv) ≫
          (χ.pageTwoCoordinateIso 0 q).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/- Page-two vertical-homology identification and representative -/


/-- Chosen second page as iterated vertical and horizontal homology.

For natural `p` and `q`, the chosen second-page object `χ.pageTwo.X (p, q)` is isomorphic to
`H_p(B.verticalHomologyComplex q)`. The isomorphism uses the inverse page transition, inverse
row-restriction homology coordinate, and the homology map of `χ.verticalHomologyIso q`. -/
noncomputable def secondPageVerticalHomologyIso
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageTwo.X (p, q) ≅
      (B.verticalHomologyComplex q).homology p :=
  (χ.pageOneTwoIso p q).symm ≪≫
    (χ.restrictionHomologyIso (χ.restrictionIndex p q)).symm ≪≫
    HomologicalComplex.homologyMapIso (χ.verticalHomologyIso q) p

/-- Zero-column representative of the inverse iterated-homology coordinate.

In horizontal degree zero, project `B.verticalHomologyComplex q` to its zeroth homology
through opcycles, then apply the inverse second-page coordinate. The same map is obtained by
the inverse component `χ.componentIso q 0`, the corresponding row-restriction projection to
zeroth homology, its homology coordinate in the first page, and the page-one-to-page-two map. -/
theorem secondPageVerticalHomologyIso_inv_representation_zero
    (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    (B.verticalHomologyComplex q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀
          (B.verticalHomologyComplex q)).inv ≫
        (χ.secondPageVerticalHomologyIso 0 q).inv =
      (χ.componentIso q 0).inv ≫
        (χ.rowRestriction q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀
          (χ.rowRestriction q)).inv ≫
        (χ.restrictionHomologyIso
          (χ.restrictionIndex 0 q)).hom ≫
        (χ.pageOneTwoIso 0 q).hom := by
  have hData :
      χ.secondPageVerticalHomologyIso 0 q =
        (χ.pageOneTwoIso 0 q).symm ≪≫
          (χ.restrictionHomologyIso
            (χ.restrictionIndex 0 q)).symm ≪≫
          HomologicalComplex.homologyMapIso
            (χ.verticalHomologyIso q) 0 := by
    rfl
  rw [hData]
  simp only [Iso.trans_inv, Iso.symm_inv,
    HomologicalComplex.homologyMapIso_inv, Category.assoc]
  rw [ChainComplex.isoHomologyι₀_inv_naturality_assoc]
  rw [HomologicalComplex.p_opcyclesMap_assoc]
  rw [χ.verticalHomologyIso_inv_f_zero q]
  rfl

end PartialTotalFirstPageChoice

end HomologicalComplex₂

end
