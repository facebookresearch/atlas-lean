/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoend
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Universal properties of a weighted coend after a preserving functor

Only preservation of the selected object and relation coproducts and selected
coequalizer is used. The enriched index remains plain; the target category and
its object/Hom universes are independent. This supplies actual tensor-preserved
coend descents and extensionality for nested Day convolution.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uD vD

namespace CategoryTheory.Enriched.weightedCoend.Mapped

open MonoidalCategory BraidedCategory Opposite Limits
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {D : Type uD} [Category.{vD} D]
  (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V) (J : V ⥤ D)

/-- The complete relation equations after applying the actual functor J. -/
abbrev Balanced {X : D} (q : ∀ a, J.obj (objects W F a) ⟶ X) : Prop :=
  ∀ a b,
    J.map ((α_ (W.obj (op b)) (a ⟶[V] b) (F.obj a)).inv ≫
      (MonoidalClosed.uncurry (W.map (op b) (op a)) ⊗ₘ 𝟙 (F.obj a))) ≫ q a =
    J.map ((W.obj (op b)) ◁
      ((β_ (a ⟶[V] b) (F.obj a)).hom ≫ MonoidalClosed.uncurry (F.map a b))) ≫ q b

section Descent

variable [HasCoproduct (relations W F)] [HasCoproduct (objects W F)]
  [PreservesColimit (Discrete.functor (relations W F)) J]

/-- Full mapped relation faces imply equality of the two mapped parallel composites. -/
theorem total_balance {X : D}
    (q : ∀ a, J.obj (objects W F a) ⟶ X)
    (d : J.obj (∐ objects W F) ⟶ X)
    (hd : ∀ a, J.map (Sigma.ι (objects W F) a) ≫ d = q a)
    (hq : Balanced W F J q) :
    J.map (leftMap W F) ≫ d = J.map (rightMap W F) ≫ d := by
  let hR := isColimitCofanMkObjOfIsColimit (G := J) (f := relations W F)
    (Sigma.ι (relations W F)) (coproductIsCoproduct (relations W F))
  apply hR.hom_ext
  intro j
  let a := j.as.1
  let b := j.as.2
  let l : relations W F (a, b) ⟶ objects W F a :=
    (α_ (W.obj (op b)) (a ⟶[V] b) (F.obj a)).inv ≫
      (MonoidalClosed.uncurry (W.map (op b) (op a)) ⊗ₘ 𝟙 (F.obj a))
  let r : relations W F (a, b) ⟶ objects W F b :=
    (W.obj (op b)) ◁
      ((β_ (a ⟶[V] b) (F.obj a)).hom ≫ MonoidalClosed.uncurry (F.map a b))
  have hl : J.map (Sigma.ι (relations W F) (a, b)) ≫ J.map (leftMap W F) =
      J.map l ≫ J.map (Sigma.ι (objects W F) a) := by
    rw [← J.map_comp]
    simp only [leftMap, Sigma.ι_comp_desc, J.map_comp, l]
  have hr : J.map (Sigma.ι (relations W F) (a, b)) ≫ J.map (rightMap W F) =
      J.map r ≫ J.map (Sigma.ι (objects W F) b) := by
    rw [← J.map_comp]
    simp only [rightMap, Sigma.ι_comp_desc, J.map_comp, r]
  change J.map (Sigma.ι (relations W F) (a, b)) ≫ (J.map (leftMap W F) ≫ d) =
    J.map (Sigma.ι (relations W F) (a, b)) ≫ (J.map (rightMap W F) ≫ d)
  calc
    _ = (J.map l ≫ J.map (Sigma.ι (objects W F) a)) ≫ d := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ d) hl
    _ = J.map l ≫ q a := by rw [Category.assoc, hd]
    _ = J.map r ≫ q b := hq a b
    _ = (J.map r ≫ J.map (Sigma.ι (objects W F) b)) ≫ d := by
      rw [Category.assoc, hd]
    _ = _ := by simpa only [Category.assoc] using congrArg (fun z => z ≫ d) hr.symm

variable [PreservesColimit (Discrete.functor (objects W F)) J]
  [HasCoequalizer (leftMap W F) (rightMap W F)]
  [PreservesColimit (parallelPair (leftMap W F) (rightMap W F)) J]

/-- Descend a genuinely balanced family after preservation of these particular colimits. -/
def desc {X : D} (q : ∀ a, J.obj (objects W F a) ⟶ X)
    (hq : Balanced W F J q) : J.obj (Enriched.weightedCoend W F) ⟶ X :=
  let hT := isColimitCofanMkObjOfIsColimit (G := J) (f := objects W F)
    (Sigma.ι (objects W F)) (coproductIsCoproduct (objects W F))
  let d := hT.desc (Cofan.mk X q)
  let hd : ∀ a, J.map (Sigma.ι (objects W F) a) ≫ d = q a :=
    fun a => hT.fac (Cofan.mk X q) (Discrete.mk a)
  let hC := isColimitCoforkMapOfIsColimit (G := J)
    (w := coequalizer.condition (leftMap W F) (rightMap W F))
    (coequalizerIsCoequalizer (leftMap W F) (rightMap W F))
  Cofork.IsColimit.desc hC d (total_balance W F J q d hd hq)

/-- The mapped descent retains every actual weighted-coend generator. -/
@[reassoc]
theorem gen_desc {X : D} (q : ∀ a, J.obj (objects W F a) ⟶ X)
    (hq : Balanced W F J q) (a : A) :
    J.map (ι W F a) ≫ desc W F J q hq = q a := by
  let hT := isColimitCofanMkObjOfIsColimit (G := J) (f := objects W F)
    (Sigma.ι (objects W F)) (coproductIsCoproduct (objects W F))
  let d : J.obj (∐ objects W F) ⟶ X := hT.desc (Cofan.mk X q)
  have hd : ∀ b, J.map (Sigma.ι (objects W F) b) ≫ d = q b :=
    fun b => hT.fac (Cofan.mk X q) (Discrete.mk b)
  let hC := isColimitCoforkMapOfIsColimit (G := J)
    (w := coequalizer.condition (leftMap W F) (rightMap W F))
    (coequalizerIsCoequalizer (leftMap W F) (rightMap W F))
  have hb : J.map (leftMap W F) ≫ d = J.map (rightMap W F) ≫ d :=
    total_balance W F J q d hd hq
  have hπ : J.map (coequalizer.π (leftMap W F) (rightMap W F)) ≫
      Cofork.IsColimit.desc hC d hb = d := Cofork.IsColimit.π_desc' hC d hb
  have hDefinition : desc W F J q hq = Cofork.IsColimit.desc hC d hb := rfl
  have hGenerator : J.map (ι W F a) =
      J.map (Sigma.ι (objects W F) a) ≫
        J.map (coequalizer.π (leftMap W F) (rightMap W F)) :=
    J.map_comp (Sigma.ι (objects W F) a)
      (coequalizer.π (leftMap W F) (rightMap W F))
  calc
    _ = J.map (ι W F a) ≫ Cofork.IsColimit.desc hC d hb :=
      congrArg (fun f => J.map (ι W F a) ≫ f) hDefinition
    _ = J.map (Sigma.ι (objects W F) a) ≫
        (J.map (coequalizer.π (leftMap W F) (rightMap W F)) ≫
          Cofork.IsColimit.desc hC d hb) := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ Cofork.IsColimit.desc hC d hb) hGenerator
    _ = J.map (Sigma.ι (objects W F) a) ≫ d :=
      congrArg (fun f => J.map (Sigma.ι (objects W F) a) ≫ f) hπ
    _ = q a := hd a

end Descent

section Extensionality

variable [HasCoproduct (relations W F)] [HasCoproduct (objects W F)]
  [HasCoequalizer (leftMap W F) (rightMap W F)]
  [PreservesColimit (Discrete.functor (objects W F)) J]
  [PreservesColimit (parallelPair (leftMap W F) (rightMap W F)) J]

/-- Mapped generators are jointly epic; preservation of the relation coproduct is unnecessary. -/
theorem hom_ext {X : D} {f g : J.obj (Enriched.weightedCoend W F) ⟶ X}
    (h : ∀ a, J.map (ι W F a) ≫ f = J.map (ι W F a) ≫ g) : f = g := by
  let hC := isColimitCoforkMapOfIsColimit (G := J)
    (w := coequalizer.condition (leftMap W F) (rightMap W F))
    (coequalizerIsCoequalizer (leftMap W F) (rightMap W F))
  apply Cofork.IsColimit.hom_ext hC
  let hT := isColimitCofanMkObjOfIsColimit (G := J) (f := objects W F)
    (Sigma.ι (objects W F)) (coproductIsCoproduct (objects W F))
  apply hT.hom_ext
  intro a
  change J.map (Sigma.ι (objects W F) a.as) ≫
      J.map (coequalizer.π (leftMap W F) (rightMap W F)) ≫ f =
    J.map (Sigma.ι (objects W F) a.as) ≫
      J.map (coequalizer.π (leftMap W F) (rightMap W F)) ≫ g
  simpa only [ι, J.map_comp, Category.assoc] using h a.as

end Extensionality

section UniversalProperty

variable [HasCoproduct (relations W F)] [HasCoproduct (objects W F)]
  [HasCoequalizer (leftMap W F) (rightMap W F)]
  [PreservesColimit (Discrete.functor (relations W F)) J]
  [PreservesColimit (Discrete.functor (objects W F)) J]
  [PreservesColimit (parallelPair (leftMap W F) (rightMap W F)) J]

/-- Maps from the preserved coend are precisely families balanced over the full hom. -/
def homEquiv (X : D) : (J.obj (Enriched.weightedCoend W F) ⟶ X) ≃
    {q : ∀ a, J.obj (objects W F a) ⟶ X // Balanced W F J q} where
  toFun f := ⟨fun a => J.map (ι W F a) ≫ f, by
    intro a b
    have h := congrArg (fun q => J.map q ≫ f) (condition W F a b)
    simpa only [J.map_comp, Category.assoc] using h⟩
  invFun q := desc W F J q.val q.property
  left_inv f := by
    apply hom_ext W F J
    intro a
    exact gen_desc W F J _ _ a
  right_inv q := by
    apply Subtype.ext
    funext a
    exact gen_desc W F J q.val q.property a

end UniversalProperty

section LiteralPresentation

/-- The original weighted-coend object family after applying the actual functor J. -/
abbrev mappedObjects : A → D := fun a => J.obj (Enriched.weightedCoend.objects W F a)
/-- The original weighted-coend relation family after applying the actual functor J. -/
abbrev mappedRelations : A × A → D :=
  fun ab => J.obj (Enriched.weightedCoend.relations W F ab)

variable [HasCoproduct (mappedObjects W F J)] [HasCoproduct (mappedRelations W F J)]

/-- The coproduct map of the actual mapped original weight faces. -/
abbrev mappedLeftMap : (∐ mappedRelations W F J) ⟶ ∐ mappedObjects W F J :=
  Sigma.desc fun ab => J.map (Enriched.weightedCoend.face0 W F ab.1 ab.2) ≫
    Sigma.ι (mappedObjects W F J) ab.1

/-- The coproduct map of the actual mapped original diagram-action faces. -/
abbrev mappedRightMap : (∐ mappedRelations W F J) ⟶ ∐ mappedObjects W F J :=
  Sigma.desc fun ab => J.map (Enriched.weightedCoend.face1 W F ab.1 ab.2) ≫
    Sigma.ι (mappedObjects W F J) ab.2

variable [HasCoproduct (Enriched.weightedCoend.objects W F)]
  [HasCoproduct (Enriched.weightedCoend.relations W F)]
  [HasCoequalizer (Enriched.weightedCoend.leftMap W F) (Enriched.weightedCoend.rightMap W F)]

/-- The actual mapped original coend is a cofork of the literal mapped faces. -/
private def mappedCofork : Cofork (mappedLeftMap W F J) (mappedRightMap W F J) :=
  Cofork.ofπ (Sigma.desc fun a => J.map (Enriched.weightedCoend.ι W F a)) (by
    apply Sigma.hom_ext
    intro ab
    simp only [mappedLeftMap, mappedRightMap, Sigma.ι_comp_desc_assoc,
      Category.assoc, Sigma.ι_comp_desc]
    rw [← J.map_comp, ← J.map_comp]
    exact congrArg J.map (Enriched.weightedCoend.condition W F ab.1 ab.2))

variable [PreservesColimit (Discrete.functor (Enriched.weightedCoend.objects W F)) J]
  [PreservesColimit (Discrete.functor (Enriched.weightedCoend.relations W F)) J]
  [PreservesColimit
    (parallelPair (Enriched.weightedCoend.leftMap W F) (Enriched.weightedCoend.rightMap W F)) J]

/-- Existing mapped-coend descent proves the full literal presentation UP. -/
private def mappedCoforkIsColimit : IsColimit (mappedCofork W F J) := by
  refine Cofork.IsColimit.mk' _ fun s => ?_
  let q (a : A) := Sigma.ι (mappedObjects W F J) a ≫ s.π
  have hq : Enriched.weightedCoend.Mapped.Balanced W F J q := by
    intro a b
    have hs := congrArg (fun z => Sigma.ι (mappedRelations W F J) (a, b) ≫ z) s.condition
    simpa only [mappedLeftMap, mappedRightMap, Sigma.ι_comp_desc_assoc, Category.assoc,
      q, Enriched.weightedCoend.face0, Enriched.weightedCoend.face1] using hs
  let d := Enriched.weightedCoend.Mapped.desc W F J q hq
  refine ⟨d, ?_, ?_⟩
  · apply Sigma.hom_ext
    intro a
    change Sigma.ι (mappedObjects W F J) a ≫
      Sigma.desc (fun b => J.map (Enriched.weightedCoend.ι W F b)) ≫ d = q a
    rw [Sigma.ι_comp_desc_assoc]
    exact Enriched.weightedCoend.Mapped.gen_desc W F J q hq a
  · intro m hm
    let m' : J.obj (Enriched.weightedCoend W F) ⟶ s.pt := m
    have hm' : Sigma.desc (fun b => J.map (Enriched.weightedCoend.ι W F b)) ≫ m' = s.π := hm
    change m' = d
    apply Enriched.weightedCoend.Mapped.hom_ext W F J
    intro a
    have ha := congrArg (fun z => Sigma.ι (mappedObjects W F J) a ≫ z) hm'
    change J.map (Enriched.weightedCoend.ι W F a) ≫ m' = _
    calc
      _ = q a := by
        change Sigma.ι (mappedObjects W F J) a ≫
          Sigma.desc (fun b => J.map (Enriched.weightedCoend.ι W F b)) ≫ m' = q a at ha
        rw [Sigma.ι_comp_desc_assoc] at ha
        exact ha
      _ = J.map (Enriched.weightedCoend.ι W F a) ≫ d :=
        (Enriched.weightedCoend.Mapped.gen_desc W F J q hq a).symm

variable [HasCoequalizer (mappedLeftMap W F J) (mappedRightMap W F J)]

/-- Compare the literal mapped-family quotient with the actual preserved coend. -/
@[no_expose]
public def mappedQuotientIso :
    coequalizer (mappedLeftMap W F J) (mappedRightMap W F J) ≅
      J.obj (Enriched.weightedCoend W F) :=
  (coequalizerIsCoequalizer (mappedLeftMap W F J) (mappedRightMap W F J)).coconePointUniqueUpToIso
    (mappedCoforkIsColimit W F J)

/-- The comparison retains every actual original mapped generator. -/
public theorem mappedQuotientIso_generator (a : A) :
    (Sigma.ι (mappedObjects W F J) a ≫
      coequalizer.π (mappedLeftMap W F J) (mappedRightMap W F J)) ≫
        (mappedQuotientIso W F J).hom = J.map (Enriched.weightedCoend.ι W F a) := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (coequalizerIsCoequalizer (mappedLeftMap W F J) (mappedRightMap W F J))
    (mappedCoforkIsColimit W F J) WalkingParallelPair.one
  change coequalizer.π (mappedLeftMap W F J) (mappedRightMap W F J) ≫
    (mappedQuotientIso W F J).hom =
      Sigma.desc (fun b => J.map (Enriched.weightedCoend.ι W F b)) at h
  rw [Category.assoc, h]
  exact Sigma.ι_comp_desc _ _

/-- A genuine coefficient natural transformation preserves the original relation
after projection. -/
theorem projectedFacesNaturality (J1 J2 : V ⥤ D) (η : J1 ⟶ J2) (a b : A) :
    J1.map (Enriched.weightedCoend.face0 W F a b) ≫ η.app (Enriched.weightedCoend.objects W F a) ≫
        J2.map (Enriched.weightedCoend.ι W F a) =
      J1.map (Enriched.weightedCoend.face1 W F a b) ≫ η.app (Enriched.weightedCoend.objects W F b) ≫
        J2.map (Enriched.weightedCoend.ι W F b) := by
  calc
    _ = η.app (Enriched.weightedCoend.relations W F (a, b)) ≫
        J2.map (Enriched.weightedCoend.face0 W F a b ≫ Enriched.weightedCoend.ι W F a) := by
      rw [← Category.assoc, η.naturality, Category.assoc, ← J2.map_comp]
    _ = η.app (Enriched.weightedCoend.relations W F (a, b)) ≫
        J2.map (Enriched.weightedCoend.face1 W F a b ≫ Enriched.weightedCoend.ι W F b) :=
      congrArg (fun f => η.app (Enriched.weightedCoend.relations W F (a, b)) ≫ J2.map f)
        (Enriched.weightedCoend.condition W F a b)
    _ = _ := by
      symm
      rw [← Category.assoc, η.naturality, Category.assoc, ← J2.map_comp]

end LiteralPresentation

end CategoryTheory.Enriched.weightedCoend.Mapped
