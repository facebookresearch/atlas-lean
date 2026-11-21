/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeRingInverseImages
public import MathlibExt.CategoryTheory.SheafKernelCompletionMaps
public import MathlibExt.CategoryTheory.SheafWittSource
public import MathlibExt.CategoryTheory.SheafLocalGeneratorLocalization

/-!
# Constructed sheaf scalar, Witt and completion maps over actual site morphisms

Finite quotients are mapped into the TARGET sheafified quotient before
the inverse limit. There is no quotient/completion of a pushed ring
substituted for the pushed target quotient/completion. The limit map
uses the native right-adjoint preservation isomorphism. The ordinary
map, all finite units and all inverse-system transitions are fixed.

The source naturality proofs below are direct Wanted proof targets;
none supplies a higher output or a final comparison map.

Native Mathlib, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
References: Scholze, arXiv:1205.3463v2, Definitions 6.1 and 6.8;
Bhatt--Morrow--Scholze, arXiv:1602.03148v3, Section 5.1.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.RingSheafMapOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Functor
open SheafScalarQuotients SheafKernelCompletion SheafWittSource NativeRingInverseImages

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {T : GrothendieckTopology D}
  [HasSheafify J CommRingCat.{1}] [HasSheafify T CommRingCat.{1}]
  (G : C ⥤ D) [G.IsContinuous J T]

abbrev ringPush := G.sheafPushforwardContinuous CommRingCat.{1} J T

section Scalars

variable (p : ℕ) (R : Sheaf J CommRingCat.{1}) (S : Sheaf T CommRingCat.{1})
  (f : R ⟶ (ringPush (J := J) (T := T) G).obj S)

/-- Sheafified mod-p map with original scalar and constant quotient units. -/
def modPMap : modP p R ⟶ (ringPush (J := J) (T := T) G).obj (modP p S) :=
  coprod.desc (f ≫ (ringPush (J := J) (T := T) G).map (modPUnit p S))
    (constantPush (J := J) (T := T) G (ZMod p) ≫ (ringPush (J := J) (T := T) G).map coprod.inr)

@[reassoc (attr := simp)] theorem modPMap_unit :
    modPUnit p R ≫ modPMap G p R S f = f ≫ (ringPush (J := J) (T := T) G).map (modPUnit p S) := by
  exact coprod.inl_desc _ _

/-- Sheafified p-inversion map; varying local denominators are retained. -/
def localizePMap : localizeP p R ⟶ (ringPush (J := J) (T := T) G).obj (localizeP p S) :=
  coprod.desc (f ≫ (ringPush (J := J) (T := T) G).map (localizePUnit p S))
    (constantPush (J := J) (T := T) G (IntegerPInversion p) ≫ (ringPush (J := J) (T := T) G).map coprod.inr)

@[reassoc (attr := simp)] theorem localizePMap_unit :
    localizePUnit p R ≫ localizePMap G p R S f = f ≫
      (ringPush (J := J) (T := T) G).map (localizePUnit p S) := by
  exact coprod.inl_desc _ _

end Scalars

section Witt

variable (p : ℕ) [Fact p.Prime] (R : Sheaf J CommRingCat.{1}) (S : Sheaf T CommRingCat.{1})
  (f : R ⟶ (ringPush (J := J) (T := T) G).obj S)

def rawWittMap : wittPresheaf p R ⟶ G.op ⋙ wittPresheaf p S where
  app U := CommRingCat.ofHom (WittVector.map (p := p) (f.hom.app U).hom)
  naturality {U V} a := by
    ext w
    apply WittVector.ext
    intro n
    exact congrArg (fun g => g.hom (w.coeff n)) (f.hom.naturality a)

def wittMap : wittSheaf p R ⟶ (ringPush (J := J) (T := T) G).obj (wittSheaf p S) :=
  ((sheafificationAdjunction J CommRingCat.{1}).homEquiv (wittPresheaf p R)
    ((ringPush (J := J) (T := T) G).obj (wittSheaf p S))).symm
      (rawWittMap G p R S f ≫ whiskerLeft G.op (toSheafify T (wittPresheaf p S)))

end Witt

section Completion

variable (R S : Sheaf J CommRingCat.{1}) (θ : R ⟶ S)
  (R' S' : Sheaf T CommRingCat.{1}) (θ' : R' ⟶ S')
  (r : R ⟶ (ringPush (J := J) (T := T) G).obj R') (s : S ⟶ (ringPush (J := J) (T := T) G).obj S')
  (square : r ≫ (ringPush (J := J) (T := T) G).map θ' = θ ≫ s)

def targetQuotientUnit (n : ℕ) :
    rawQuotient ((ringPush (J := J) (T := T) G).obj R') ((ringPush (J := J) (T := T) G).obj S') ((ringPush (J := J) (T := T) G).map θ') n ⟶
      ((ringPush (J := J) (T := T) G).obj (quotientSheaf R' S' θ' n)).obj where
  app U := (toSheafify T (rawQuotient R' S' θ' n)).app (G.op.obj U)
  naturality {U V} f := by
    change (rawQuotient R' S' θ' n).map (G.op.map f) ≫
      (toSheafify T (rawQuotient R' S' θ' n)).app (G.op.obj V) =
        (toSheafify T (rawQuotient R' S' θ' n)).app (G.op.obj U) ≫
          (sheafify T (rawQuotient R' S' θ' n)).map (G.op.map f)
    exact (toSheafify T (rawQuotient R' S' θ' n)).naturality (G.op.map f)

def rawQuotientMap (n : ℕ) : rawQuotient R S θ n ⟶
    ((ringPush (J := J) (T := T) G).obj (quotientSheaf R' S' θ' n)).obj :=
  SheafKernelCompletionMaps.rawMap R S ((ringPush (J := J) (T := T) G).obj R') ((ringPush (J := J) (T := T) G).obj S')
    θ ((ringPush (J := J) (T := T) G).map θ') r s square n ≫ targetQuotientUnit G R' S' θ' n

def quotientMap (n : ℕ) : quotientSheaf R S θ n ⟶ (ringPush (J := J) (T := T) G).obj (quotientSheaf R' S' θ' n) :=
  ((sheafificationAdjunction J CommRingCat.{1}).homEquiv (rawQuotient R S θ n)
    ((ringPush (J := J) (T := T) G).obj (quotientSheaf R' S' θ' n))).symm (rawQuotientMap G R S θ R' S' θ' r s square n)

/-- A direct source proof target for the FIXED native finite quotient maps. -/
def CompletionNaturality : Prop :=
  ∀ {n m : ℕᵒᵖ} (h : n ⟶ m),
    (tower R S θ).map h ≫ quotientMap G R S θ R' S' θ' r s square m.unop =
      quotientMap G R S θ R' S' θ' r s square n.unop ≫ (ringPush (J := J) (T := T) G).map ((tower R' S' θ').map h)

def quotientTowerMap (h : CompletionNaturality G R S θ R' S' θ' r s square) :
    tower R S θ ⟶ tower R' S' θ' ⋙ ringPush (J := J) (T := T) G where
  app n := quotientMap G R S θ R' S' θ' r s square n.unop
  naturality {n m} a := h a

variable [(ringPush (J := J) (T := T) G).IsRightAdjoint]

/-- Native limit map to the ACTUAL pushed target completion. -/
def completionMap (h : CompletionNaturality G R S θ R' S' θ' r s square) :
    completion R S θ ⟶ (ringPush (J := J) (T := T) G).obj (completion R' S' θ') :=
  limMap (quotientTowerMap G R S θ R' S' θ' r s square h) ≫
    (preservesLimitIso (ringPush (J := J) (T := T) G) (tower R' S' θ')).inv

end Completion

section EndLimits

variable (R : Sheaf J CommRingCat.{1}) (S : Sheaf T CommRingCat.{1})
  (r : R ⟶ (ringPush (J := J) (T := T) G).obj S) (e : End R) (f : End S)

def EndTowerNaturality : Prop :=
  ∀ {n m : ℕᵒᵖ} (h : n ⟶ m),
    (inverseEndTower R e).map h ≫ r = r ≫ (ringPush (J := J) (T := T) G).map ((inverseEndTower S f).map h)

def endTowerMap (h : EndTowerNaturality G R S r e f) :
    inverseEndTower R e ⟶ inverseEndTower S f ⋙ ringPush (J := J) (T := T) G where
  app _ := r
  naturality {n m} a := h a

variable [(ringPush (J := J) (T := T) G).IsRightAdjoint]

def endLimitMap (h : EndTowerNaturality G R S r e f) :
    limit (inverseEndTower R e) ⟶ (ringPush (J := J) (T := T) G).obj (limit (inverseEndTower S f)) :=
  limMap (endTowerMap G R S r e f h) ≫ (preservesLimitIso (ringPush (J := J) (T := T) G) (inverseEndTower S f)).inv

end EndLimits

section Localizations

open SheafLocalGeneratorLocalization

variable (AY HY RY : Sheaf J CommRingCat.{1}) (θY : AY ⟶ HY) (aY : AY ⟶ RY)
  (AX HX RX : Sheaf T CommRingCat.{1}) (θX : AX ⟶ HX) (aX : AX ⟶ RX)
  (fA : AY ⟶ (ringPush (J := J) (T := T) G).obj AX)
  (fR : RY ⟶ (ringPush (J := J) (T := T) G).obj RX)
  (square : aY ≫ fR = fA ≫ (ringPush (J := J) (T := T) G).map aX)
  (generators : ∀ (U : Cᵒᵖ) (t : AY.obj.obj U), IsLocalGenerator AY HY θY U t →
    IsLocalGenerator AX HX θX (G.op.obj U) ((fA.hom.app U).hom t))

include square generators in
theorem denominatorsMap (U : Cᵒᵖ) : denominators AY HY RY θY aY U ≤
    (denominators AX HX RX θX aX (G.op.obj U)).comap (fR.hom.app U).hom := by
  apply Submonoid.closure_le.mpr
  rintro _ ⟨t, ht, rfl⟩
  apply Submonoid.subset_closure
  refine ⟨(fA.hom.app U).hom t, generators U t ht, ?_⟩
  exact (congrArg (fun f => (f.hom.app U).hom t) square).symm

def rawLocalizationMap : rawLocalization AY HY RY θY aY ⟶ G.op ⋙ rawLocalization AX HX RX θX aX where
  app U := CommRingCat.ofHom
    (IsLocalization.map (Localization (denominators AX HX RX θX aX (G.op.obj U)))
      (show RY.obj.obj U →+* RX.obj.obj (G.op.obj U) from (fR.hom.app U).hom)
      (denominatorsMap G AY HY RY θY aY AX HX RX θX aX fA fR square generators U))
  naturality {U V} f := by
    dsimp [rawLocalization]
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (denominators AY HY RY θY aY U)
    ext x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, IsLocalization.map_eq]
    exact congrArg (algebraMap (RX.obj.obj (G.op.obj V))
      (Localization (denominators AX HX RX θX aX (G.op.obj V))))
      (congrArg (fun g => g.hom x) (fR.hom.naturality f))

/-- Actual full-period map from local absolute-generator localizations and TARGET sheafification. -/
def localizationMap : localization AY HY RY θY aY ⟶
    (ringPush (J := J) (T := T) G).obj (localization AX HX RX θX aX) :=
  ((sheafificationAdjunction J CommRingCat.{1}).homEquiv (rawLocalization AY HY RY θY aY)
    ((ringPush (J := J) (T := T) G).obj (localization AX HX RX θX aX))).symm
      (rawLocalizationMap G AY HY RY θY aY AX HX RX θX aX fA fR square generators ≫
        whiskerLeft G.op (toSheafify T (rawLocalization AX HX RX θX aX)))

end Localizations

end MathlibExt.CategoryTheory.RingSheafMapOperations
