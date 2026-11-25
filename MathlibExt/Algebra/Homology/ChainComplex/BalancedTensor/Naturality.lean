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

public import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor.HomIso

/-!
# Naturality of the full signed tensor–Hom total adjunction

The right and left module complexes vary contravariantly in Hom, and the
abelian target varies covariantly. Every map below is the native tensor or
Hom map already used to define the two actual total complexes.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace ChainComplex.BalancedTensor

universe u v

variable (R : Type u) [Ring R]

/-- The earned enriched inner-Hom map has the original pointwise pre/postcomposition. -/
theorem moduleHomMap_v
    {Q Q' : ChainComplex (ModuleCat.{v} R) ℤ}
    {I I' : CochainComplex AddCommGrpCat.{v} ℤ}
    (g : Q' ⟶ Q) (h : I ⟶ I') (b c d : ℤ) (hcd : c + b = d)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence AddCommGrpCat).functor.obj
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.down ℤ)).obj Q)) I b)
    (y : Q'.X (-c)) :
    ((((moduleHomCochainComplexMap R g h).f b).hom z).v c d hcd).hom y =
      (h.f d).hom ((z.v c d hcd).hom ((g.f (-c)).hom y)) := by
  let U := (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex
    (ComplexShape.down ℤ)
  let C := (cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj (U.obj Q)
  let C' := (cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj (U.obj Q')
  let A : AddCommGrpCat.{v} := C.X c
  let A' : AddCommGrpCat.{v} := C'.X c
  let pre : A' ⟶ A :=
    ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.map (U.map g)).f c
  let pre₀ : A' ⟶ A :=
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).map (g.f (-c))
  have hPre : pre = pre₀ := rfl
  let y₀ : A' := y
  have hPreValue : pre.hom y₀ = (g.f (-c)).hom y :=
    (congrArg (fun m : A' ⟶ A => m.hom y₀) hPre).trans
      (show pre₀.hom y₀ = (g.f (-c)).hom y from rfl)
  let f : A ⟶ I.X d := z.v c d hcd
  let post : I.X d ⟶ I'.X d := h.f d
  let δz : A' ⟶ I'.X d :=
    (((homCochainComplexMap (U.map g) h).f b).hom z).v c d hcd
  have hMaps : δz = pre ≫ f ≫ post :=
    homCochainComplexMap_v (U.map g) h b c d hcd z
  have hValue := congrArg (fun m : A' ⟶ I'.X d => m.hom y₀) hMaps
  have hComposeFirst : (pre ≫ f ≫ post).hom y₀ = (f ≫ post).hom (pre.hom y₀) :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_comp pre (f ≫ post)) y₀).trans
      (AddMonoidHom.comp_apply (f ≫ post).hom pre.hom y₀)
  have hComposeSecond : (f ≫ post).hom (pre.hom y₀) =
      post.hom (f.hom (pre.hom y₀)) :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_comp f post) (pre.hom y₀)).trans
      (AddMonoidHom.comp_apply post.hom f.hom (pre.hom y₀))
  have he' : ((((homCochainComplexMap (U.map g) h).f b).hom z).v c d hcd).hom y =
      (h.f d).hom ((z.v c d hcd).hom ((g.f (-c)).hom y)) :=
    hValue.trans (hComposeFirst.trans (hComposeSecond.trans
      (congrArg (fun value : A => post.hom (f.hom value)) hPreValue)))
  have hm : ((moduleHomCochainComplexMap R g h).f b).hom z =
      ((homCochainComplexMap (U.map g) h).f b).hom z := rfl
  have hmPoint := congrArg (fun w : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence AddCommGrpCat).functor.obj (U.obj Q')) I' b =>
      (w.v c d hcd).hom y) hm
  exact hmPoint.trans he'

/-- Signed currying commutes with the actual maps in all three original variables. -/
theorem curryCochain_naturality
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q Q' : ChainComplex (ModuleCat.{v} R) ℤ}
    {I I' : CochainComplex AddCommGrpCat.{v} ℤ}
    (f : P' ⟶ P) (g : Q' ⟶ Q) (h : I ⟶ I') (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence AddCommGrpCat).functor.obj (complex R P Q)) I n) :
    curryCochain R P' Q' I' n
        (((homCochainComplexMap (map R f g) h).f n).hom z) =
      ((homCochainComplexMap f (moduleHomCochainComplexMap R g h)).f n).hom
        (curryCochain R P Q I n z) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro a b hab
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply CochainComplex.HomComplex.Cochain.ext
  intro c d hcd
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro y
  let xp := (f.f (-a)).hom x
  let yq := (g.f (-c)).hom y
  let w := mk R P' Q' (-a) (-c) (-(a + c)) (by omega) x y
  let w' := mk R P Q (-a) (-c) (-(a + c)) (by omega) xp yq
  have ht : ((map R f g).f (-(a + c))).hom w = w' :=
    map_mk R f g (-a) (-c) (-(a + c)) (by omega) x y
  have hl0 := homCochainComplexMap_v (map R f g) h n (a + c) d (by omega) z
  have hl1 := congrArg (fun k :
      ((cochainComplexEquivalence AddCommGrpCat).functor.obj (complex R P' Q')).X
        (a + c) ⟶ I'.X d => k.hom w) hl0
  have hl2 :
      ((((homCochainComplexMap (map R f g) h).f n).hom z).v
        (a + c) d (by omega)).hom w =
      (h.f d).hom ((z.v (a + c) d (by omega)).hom w') := by
    have hl3 :
        ((((homCochainComplexMap (map R f g) h).f n).hom z).v
          (a + c) d (by omega)).hom w =
        (h.f d).hom ((z.v (a + c) d (by omega)).hom
          (((map R f g).f (-(a + c))).hom w)) := by
      let T₀ : AddCommGrpCat.{v} :=
        ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj
          (complex R P' Q')).X (a + c)
      let T₁ : AddCommGrpCat.{v} :=
        ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj
          (complex R P Q)).X (a + c)
      let pre : T₀ ⟶ T₁ :=
        ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.map
          (map R f g)).f (a + c)
      let pre₀ : T₀ ⟶ T₁ := (map R f g).f (-(a + c))
      have hReindex : pre = pre₀ := rfl
      have hPreValue : pre.hom w = pre₀.hom w :=
        congrArg (fun m : T₀ ⟶ T₁ => m.hom w) hReindex
      let component : T₁ ⟶ I.X d := z.v (a + c) d (by omega)
      let post : I.X d ⟶ I'.X d := h.f d
      let rest : T₁ ⟶ I'.X d := component ≫ post
      let value : T₀ ⟶ I'.X d :=
        (((homCochainComplexMap (map R f g) h).f n).hom z).v
          (a + c) d (by omega)
      have hArrow : value = pre ≫ rest := hl0
      have hOuter : (pre ≫ rest).hom w = rest.hom (pre.hom w) :=
        (DFunLike.congr_fun (AddCommGrpCat.hom_comp pre rest) w).trans
          (AddMonoidHom.comp_apply rest.hom pre.hom w)
      have hInner : rest.hom (pre.hom w) =
          post.hom (component.hom (pre.hom w)) :=
        (DFunLike.congr_fun (AddCommGrpCat.hom_comp component post)
          (pre.hom w)).trans
            (AddMonoidHom.comp_apply post.hom component.hom (pre.hom w))
      exact (congrArg (fun m : T₀ ⟶ I'.X d => m.hom w) hArrow).trans
        (hOuter.trans (hInner.trans (congrArg
          (fun t : T₁ => post.hom (component.hom t)) hPreValue)))
    exact hl3.trans (congrArg (fun t =>
      (h.f d).hom ((z.v (a + c) d (by omega)).hom t)) ht)
  have hcLeft := curryCochain_v R P' Q' I' n
    (((homCochainComplexMap (map R f g) h).f n).hom z) a b hab c d hcd x y
  have hl :
      ((((curryCochain R P' Q' I' n
        (((homCochainComplexMap (map R f g) h).f n).hom z)).v a b hab).hom x).v
          c d hcd).hom y =
      Int.triangularSign b • (h.f d).hom ((z.v (a + c) d (by omega)).hom w') :=
    hcLeft.trans (congrArg (fun t : I'.X d => Int.triangularSign b • t) hl2)
  have hr0 := homCochainComplexMap_v f (moduleHomCochainComplexMap R g h)
    n a b hab (curryCochain R P Q I n z)
  have hr1 := congrArg (fun k :
      ((cochainComplexEquivalence (ModuleCat Rᵐᵒᵖ)).functor.obj P').X a ⟶
        (moduleHomCochainComplex R Q' I').X b => k.hom x) hr0
  have hr2 :
      ((((homCochainComplexMap f (moduleHomCochainComplexMap R g h)).f n).hom
        (curryCochain R P Q I n z)).v a b hab).hom x =
      ((moduleHomCochainComplexMap R g h).f b).hom
        (((curryCochain R P Q I n z).v a b hab).hom xp) := by
    let A₀ : ModuleCat.{v} Rᵐᵒᵖ :=
      ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P').X a
    let A₁ : ModuleCat.{v} Rᵐᵒᵖ :=
      ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P).X a
    let B₀ : ModuleCat.{v} Rᵐᵒᵖ := (moduleHomCochainComplex R Q I).X b
    let B₁ : ModuleCat.{v} Rᵐᵒᵖ := (moduleHomCochainComplex R Q' I').X b
    let pre : A₀ ⟶ A₁ :=
      ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.map f).f a
    let pre₀ : A₀ ⟶ A₁ := f.f (-a)
    have hReindex : pre = pre₀ := rfl
    have hPreValue : pre.hom x = pre₀.hom x :=
      congrArg (fun m : A₀ ⟶ A₁ => m.hom x) hReindex
    let component : A₁ ⟶ B₀ := (curryCochain R P Q I n z).v a b hab
    let post : B₀ ⟶ B₁ := (moduleHomCochainComplexMap R g h).f b
    let rest : A₁ ⟶ B₁ := component ≫ post
    let value : A₀ ⟶ B₁ :=
      (((homCochainComplexMap f (moduleHomCochainComplexMap R g h)).f n).hom
        (curryCochain R P Q I n z)).v a b hab
    have hArrow : value = pre ≫ rest := hr0
    have hOuter : (pre ≫ rest).hom x = rest.hom (pre.hom x) :=
      (DFunLike.congr_fun (ModuleCat.hom_comp pre rest) x).trans
        (LinearMap.comp_apply rest.hom pre.hom x)
    have hInner : rest.hom (pre.hom x) = post.hom (component.hom (pre.hom x)) :=
      (DFunLike.congr_fun (ModuleCat.hom_comp component post) (pre.hom x)).trans
        (LinearMap.comp_apply post.hom component.hom (pre.hom x))
    exact (congrArg (fun m : A₀ ⟶ B₁ => m.hom x) hArrow).trans
      (hOuter.trans (hInner.trans (congrArg
        (fun t : A₁ => post.hom (component.hom t)) hPreValue)))
  have hr3 := congrArg (fun t : CochainComplex.HomComplex.Cochain
      ((cochainComplexEquivalence AddCommGrpCat).functor.obj
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.down ℤ)).obj Q')) I' b =>
      (t.v c d hcd).hom y) hr2
  have hr4 := moduleHomMap_v R g h b c d hcd
    (((curryCochain R P Q I n z).v a b hab).hom xp) y
  have hcRight := curryCochain_v R P Q I n z a b hab c d hcd xp yq
  have hr5 := congrArg (h.f d).hom hcRight
  have hr :
      ((((((homCochainComplexMap f (moduleHomCochainComplexMap R g h)).f n).hom
        (curryCochain R P Q I n z)).v a b hab).hom x).v c d hcd).hom y =
      Int.triangularSign b • (h.f d).hom ((z.v (a + c) d (by omega)).hom w') := by
    have hp := hr3.trans (hr4.trans hr5)
    simpa only [map_zsmul_unit, yq, w'] using hp
  exact hl.trans hr.symm

/-- The native complex isomorphism is natural in the right module, left module, and target. -/
theorem homIso_naturality
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q Q' : ChainComplex (ModuleCat.{v} R) ℤ}
    {I I' : CochainComplex AddCommGrpCat.{v} ℤ}
    (f : P' ⟶ P) (g : Q' ⟶ Q) (h : I ⟶ I') :
    homCochainComplexMap (map R f g) h ≫ (homIso R P' Q' I').hom =
      (homIso R P Q I).hom ≫
        homCochainComplexMap f (moduleHomCochainComplexMap R g h) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  change curryCochain R P' Q' I' n
      (((homCochainComplexMap (map R f g) h).f n).hom z) =
    ((homCochainComplexMap f (moduleHomCochainComplexMap R g h)).f n).hom
      (curryCochain R P Q I n z)
  exact curryCochain_naturality R f g h n z

end ChainComplex.BalancedTensor
