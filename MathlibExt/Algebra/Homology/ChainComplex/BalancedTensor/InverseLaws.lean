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

public import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor.Uncurry

/-!
# Index transport for total tensor–Hom inverse laws

The transports are the negative-reindexing unit and object equality
isomorphisms, with the full integer index range retained.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace ChainComplex.BalancedTensor

private theorem source_v_of_eq {C : Type*} [Category* C] [Preadditive C]
    {A B : CochainComplex C ℤ} {n : ℤ}
    (f : CochainComplex.HomComplex.Cochain A B n)
    (p p' q : ℤ) (h : p = p') (hpq : p + n = q) :
    (A.XIsoOfEq h).hom ≫ f.v p' q (by cases h; exact hpq) = f.v p q hpq := by
  cases h
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, Category.id_comp]

universe u v

variable (R : Type u) [Ring R]
  (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
  (Q : ChainComplex (ModuleCat.{v} R) ℤ)
  (I : CochainComplex AddCommGrpCat.{v} ℤ)

local notation "HI" => moduleHomCochainComplex R Q I

/-- The actual native unit cancels the source-index transport in every integer degree. -/
theorem unit_source_v (n : ℤ) (g : CochainComplex.HomComplex.Cochain
    ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P) HI n)
    (a b : ℤ) (hab : a + n = b) (x : P.X (-a)) :
    (g.v (-(-a)) b (by omega)).hom
        ((((cochainComplexEquivalence (ModuleCat Rᵐᵒᵖ)).unitIso.app P).hom.f (-a)).hom x) =
      (g.v a b hab).hom x := by
  let A := (cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P
  let B := moduleHomCochainComplex R Q I
  let u : A.X a ⟶ A.X (-(-a)) :=
    (((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).unitIso.app P).hom.f (-a))
  let k : A.X (-(-a)) ⟶ B.X b := g.v (-(-a)) b (by omega)
  have h : a = -(-a) := (neg_neg a).symm
  have hu : u = (A.XIsoOfEq h).hom := rfl
  have hv := source_v_of_eq g a (-(-a)) b h hab
  have hArrow : u ≫ k = g.v a b hab := by
    exact (congrArg (fun f : A.X a ⟶ A.X (-(-a)) => f ≫ k) hu).trans hv
  let x₀ : A.X a := x
  have hValue := congrArg (fun f : A.X a ⟶ B.X b => f.hom x₀) hArrow
  have hCompose : (u ≫ k).hom x₀ = k.hom (u.hom x₀) :=
    (DFunLike.congr_fun (ModuleCat.hom_comp u k) x₀).trans
      (LinearMap.comp_apply k.hom u.hom x₀)
  change k.hom (u.hom x₀) = (g.v a b hab).hom x₀
  exact hCompose.symm.trans hValue

/-- The original left-module unit cancels the inner source-index transport after forgetting. -/
theorem unit_inner_v (b : ℤ) (g : CochainComplex.HomComplex.Cochain
    (ChainComplex.moduleHomDomainCochain R Q) I b)
    (c d : ℤ) (hcd : c + b = d) (y : Q.X (-c)) :
    (g.v (-(-c)) d (by omega)).hom
        ((((cochainComplexEquivalence (ModuleCat R)).unitIso.app Q).hom.f (-c)).hom y) =
      (g.v c d hcd).hom y := by
  let U := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  let A := ChainComplex.moduleHomDomainCochain R Q
  let u : Q.X (-c) ⟶ Q.X (-(-(-c))) :=
    (((cochainComplexEquivalence (ModuleCat.{v} R)).unitIso.app Q).hom.f (-c))
  let u₀ : A.X c ⟶ A.X (-(-c)) := U.map u
  let k : A.X (-(-c)) ⟶ I.X d := g.v (-(-c)) d (by omega)
  have h : c = -(-c) := (neg_neg c).symm
  have hu : u₀ = (A.XIsoOfEq h).hom := by
    have map_eqToHom {X Y : ModuleCat.{v} R} (e : X = Y) :
        U.map (eqToHom e) = eqToHom (congrArg U.obj e) := by
      cases e
      simpa only [eqToHom_refl] using U.map_id X
    let e : Q.X (-c) = Q.X (-(-(-c))) := by congr 1; simp
    change U.map (eqToHom e) = eqToHom (congrArg U.obj e)
    exact map_eqToHom e
  have hv := source_v_of_eq g c (-(-c)) d h hcd
  have hArrow : u₀ ≫ k = g.v c d hcd :=
    (congrArg (fun f : A.X c ⟶ A.X (-(-c)) => f ≫ k) hu).trans hv
  let y₀ : A.X c := y
  have hValue := congrArg (fun f : A.X c ⟶ I.X d => f.hom y₀) hArrow
  have hCompose : (u₀ ≫ k).hom y₀ = k.hom (u₀.hom y₀) :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_comp u₀ k) y₀).trans
      (AddMonoidHom.comp_apply k.hom u₀.hom y₀)
  have hUnit : u₀.hom y₀ = u.hom y := rfl
  change k.hom (u.hom y) = (g.v c d hcd).hom y₀
  exact (congrArg k.hom hUnit).symm.trans (hCompose.symm.trans hValue)

/-- Native equality isomorphisms transport a pure tensor and its original Hom evaluation. -/
theorem tensor_v_of_eq (n : ℤ)
    (f : CochainComplex.HomComplex.Cochain
        ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj (complex R P Q)) I n)
    (a d : ℤ) (had : a + n = d) (p q : ℤ) (hpq : p + q = -a)
    (p' q' a' : ℤ) (hp : p = p') (hq : q = q') (ha : a = a')
    (x : P.X p) (y : Q.X q) :
    (f.v a' d (by omega)).hom
        (mk R P Q p' q' (-a') (by omega)
          ((P.XIsoOfEq hp).hom.hom x) ((Q.XIsoOfEq hq).hom.hom y)) =
      (f.v a d had).hom (mk R P Q p q (-a) hpq x y) := by
  cases hp
  cases hq
  cases ha
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    ModuleCat.hom_id, LinearMap.id_apply]

/-- Uncurrying after currying fixes every original tensor-total Hom cochain. -/
theorem uncurry_curry (n : ℤ) (f : CochainComplex.HomComplex.Cochain
    ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj (complex R P Q)) I n) :
    uncurryCochain R P Q I n (curryCochain R P Q I n f) = f := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro a d had
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = -a at hpq
  apply ModuleCat.BalancedTensor.groupHom_ext R (P.X p) (Q.X q) (I.X d)
  intro x y
  let : Module ℤ (Q.X q) := Module.compHom (Q.X q) (algebraMap ℤ R)
  let b : ℤ := -p + n
  let uP : P.X p ⟶ P.X (-(-p)) :=
    (((cochainComplexEquivalence (ModuleCat Rᵐᵒᵖ)).unitIso.app P).hom.f p)
  let uQ : Q.X q ⟶ Q.X (-(-q)) :=
    (((cochainComplexEquivalence (ModuleCat R)).unitIso.app Q).hom.f q)
  let xp : P.X (-(-p)) := uP.hom x
  let yq : Q.X (-(-q)) := uQ.hom y
  have hu := uncurryCochain_mk R P Q I n (curryCochain R P Q I n f)
    a d had p q hpq x y
  have hc := curryCochain_v R P Q I n f (-p) b rfl (-q) d
    (by dsimp [b]; omega) xp yq
  let hp₀ : p = -(-p) := by simp
  let hq₀ : q = -(-q) := by simp
  let ha₀ : a = -p + -q := by omega
  have he := tensor_v_of_eq R P Q I n f a d had p q hpq
    (-(-p)) (-(-q)) (-p + -q) hp₀ hq₀ ha₀ x y
  have hp : uP = (P.XIsoOfEq hp₀).hom := rfl
  have hq : uQ = (Q.XIsoOfEq hq₀).hom := rfl
  have hx : xp = (P.XIsoOfEq hp₀).hom.hom x :=
    congrArg (fun u : P.X p ⟶ P.X (-(-p)) => u.hom x) hp
  have hy : yq = (Q.XIsoOfEq hq₀).hom.hom y :=
    congrArg (fun u : Q.X q ⟶ Q.X (-(-q)) => u.hom y) hq
  have hTensor : mk R P Q (-(-p)) (-(-q)) (-(-p + -q)) (by omega) xp yq =
      mk R P Q (-(-p)) (-(-q)) (-(-p + -q)) (by omega)
        ((P.XIsoOfEq hp₀).hom.hom x) ((Q.XIsoOfEq hq₀).hom.hom y) :=
    congrArg₂ (fun x' : P.X (-(-p)) => fun y' : Q.X (-(-q)) =>
      mk R P Q (-(-p)) (-(-q)) (-(-p + -q)) (by omega) x' y') hx hy
  have hvalue : (f.v (-p + -q) d (by omega)).hom
      (mk R P Q (-(-p)) (-(-q)) (-(-p + -q)) (by omega) xp yq) =
      (f.v a d had).hom (mk R P Q p q (-a) hpq x y) :=
    (congrArg (f.v (-p + -q) d (by omega)).hom hTensor).trans he
  have hresult := hu.trans (congrArg (fun z : I.X d => Int.triangularSign b • z)
    (hc.trans (congrArg (fun z : I.X d => Int.triangularSign b • z) hvalue)))
  let A : AddCommGrpCat.{v} :=
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.X p)).obj (Q.X q)
  let T : AddCommGrpCat.{v} := (complex R P Q).X (-a)
  let z : A := TensorProduct.Balanced.mk ℤ R (P.X p) (Q.X q) x y
  let ι : A ⟶ T := HomologicalComplex.ιMapBifunctor P Q
    (ModuleCat.BalancedTensor.groupBifunctor R) (ComplexShape.down ℤ) p q (-a)
    (by change p + q = -a; exact hpq)
  let l : T ⟶ I.X d := (uncurryCochain R P Q I n (curryCochain R P Q I n f)).v a d had
  let r : T ⟶ I.X d := f.v a d had
  have hRaw : ((uncurryCochain R P Q I n (curryCochain R P Q I n f)).v a d had).hom
      (mk R P Q p q (-a) hpq x y) = (f.v a d had).hom (mk R P Q p q (-a) hpq x y) := by
    simpa only [smul_smul, Int.units_mul_self, one_smul] using hresult
  have hMk : mk R P Q p q (-a) hpq x y = ι.hom z := rfl
  have hPoint : l.hom (ι.hom z) = r.hom (ι.hom z) :=
    (congrArg l.hom hMk).symm.trans (hRaw.trans (congrArg r.hom hMk))
  have hLeft : (ι ≫ l).hom z = l.hom (ι.hom z) :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_comp ι l) z).trans
      (AddMonoidHom.comp_apply l.hom ι.hom z)
  have hRight : (ι ≫ r).hom z = r.hom (ι.hom z) :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_comp ι r) z).trans
      (AddMonoidHom.comp_apply r.hom ι.hom z)
  exact hLeft.trans (hPoint.trans hRight.symm)

/-- Currying after uncurrying fixes every original nested full-product Hom cochain. -/
theorem curry_uncurry (n : ℤ) (g : CochainComplex.HomComplex.Cochain
    ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P) HI n) :
    curryCochain R P Q I n (uncurryCochain R P Q I n g) = g := by
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
  let x₀ : P.X (-a) := x
  let y₀ : Q.X (-c) := y
  let xp := (((cochainComplexEquivalence (ModuleCat Rᵐᵒᵖ)).unitIso.app P).hom.f (-a)).hom x₀
  let yq := (((cochainComplexEquivalence (ModuleCat R)).unitIso.app Q).hom.f (-c)).hom y₀
  have hu := uncurryCochain_mk R P Q I n g (a + c) d (by omega)
    (-a) (-c) (by omega) x₀ y₀
  have hb : -(-a) + n = b := by omega
  have hu' : ((uncurryCochain R P Q I n g).v (a + c) d (by omega)).hom
      (mk R P Q (-a) (-c) (-(a + c)) (by omega) x₀ y₀) =
      Int.triangularSign b •
        (((g.v (-(-a)) b (by omega)).hom xp).v (-(-c)) d (by omega)).hom yq := by
    cases hb
    simpa only [xp, yq] using hu
  have hSource := unit_source_v R P Q I n g a b hab x₀
  have hSourcePoint := congrArg
    (fun z : CochainComplex.HomComplex.Cochain (ChainComplex.moduleHomDomainCochain R Q) I b =>
      (z.v (-(-c)) d (by omega)).hom yq) hSource
  have hInner := unit_inner_v R Q I b ((g.v a b hab).hom x₀) c d hcd y₀
  have hValue := hSourcePoint.trans hInner
  have hAdjusted := hu'.trans
    (congrArg (fun z : I.X d => Int.triangularSign b • z) hValue)
  have hc := curryCochain_v R P Q I n (uncurryCochain R P Q I n g)
    a b hab c d hcd x₀ y₀
  have hresult := hc.trans
    (congrArg (fun z : I.X d => Int.triangularSign b • z) hAdjusted)
  simpa only [smul_smul, Int.units_mul_self, one_smul] using hresult

/-- Currying is additive on the original native products. -/
theorem curryCochain_add (n : ℤ) (f g : CochainComplex.HomComplex.Cochain
    ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj (complex R P Q)) I n) :
    curryCochain R P Q I n (f + g) =
      curryCochain R P Q I n f + curryCochain R P Q I n g := by
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
  let x₀ : P.X (-a) := x
  let y₀ : Q.X (-c) := y
  let A : ModuleCat.{v} Rᵐᵒᵖ :=
    ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P).X a
  let B : ModuleCat.{v} Rᵐᵒᵖ := (moduleHomCochainComplex R Q I).X b
  let S : AddCommGrpCat.{v} :=
    ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj (complex R P Q)).X (a + c)
  let z : S := mk R P Q (-a) (-c) (-(a + c)) (by omega) x₀ y₀
  let h : a + c + n = d := by omega
  let zf := ((curryCochain R P Q I n f).v a b hab).hom x₀
  let zg := ((curryCochain R P Q I n g).v a b hab).hom x₀
  have hSource := CochainComplex.HomComplex.Cochain.add_v f g (a + c) d h
  have hSourcePoint : ((f + g).v (a + c) d h).hom z =
      (f.v (a + c) d h).hom z + (g.v (a + c) d h).hom z :=
    (congrArg (fun m : S ⟶ I.X d => m.hom z) hSource).trans
      ((DFunLike.congr_fun (AddCommGrpCat.hom_add (f.v (a + c) d h) (g.v (a + c) d h)) z).trans
        (AddMonoidHom.add_apply (f.v (a + c) d h).hom (g.v (a + c) d h).hom z))
  have hPlus := curryCochain_v R P Q I n (f + g) a b hab c d hcd x₀ y₀
  have hF := curryCochain_v R P Q I n f a b hab c d hcd x₀ y₀
  have hG := curryCochain_v R P Q I n g a b hab c d hcd x₀ y₀
  have hScalar := (congrArg (fun v : I.X d => Int.triangularSign b • v) hSourcePoint).trans
    (smul_add (Int.triangularSign b) ((f.v (a + c) d h).hom z) ((g.v (a + c) d h).hom z))
  have hLeft := hPlus.trans (hScalar.trans
    (congrArg₂ (fun v w : I.X d => v + w) hF.symm hG.symm))
  have hOuter := CochainComplex.HomComplex.Cochain.add_v
    (curryCochain R P Q I n f) (curryCochain R P Q I n g) a b hab
  have hOuterPoint :
      (((curryCochain R P Q I n f + curryCochain R P Q I n g).v a b hab).hom x₀) = zf + zg :=
    (congrArg (fun m : A ⟶ B => m.hom x₀) hOuter).trans
      ((DFunLike.congr_fun (ModuleCat.hom_add
        ((curryCochain R P Q I n f).v a b hab) ((curryCochain R P Q I n g).v a b hab)) x₀).trans
          (LinearMap.add_apply ((curryCochain R P Q I n f).v a b hab).hom
            ((curryCochain R P Q I n g).v a b hab).hom x₀))
  have hInner := CochainComplex.HomComplex.Cochain.add_v zf zg c d hcd
  have hInnerPoint : ((zf + zg).v c d hcd).hom y₀ =
      (zf.v c d hcd).hom y₀ + (zg.v c d hcd).hom y₀ :=
    (congrArg (fun m : (ChainComplex.moduleHomDomainCochain R Q).X c ⟶ I.X d => m.hom y₀)
      hInner).trans
      ((DFunLike.congr_fun (AddCommGrpCat.hom_add (zf.v c d hcd) (zg.v c d hcd)) y₀).trans
        (AddMonoidHom.add_apply (zf.v c d hcd).hom (zg.v c d hcd).hom y₀))
  have hRight := (congrArg
    (fun w : CochainComplex.HomComplex.Cochain (ChainComplex.moduleHomDomainCochain R Q) I b =>
      (w.v c d hcd).hom y₀) hOuterPoint).trans hInnerPoint
  exact hLeft.trans hRight.symm

/-- The actual degreewise signed tensor–Hom equivalence, on the native sum and products. -/
def cochainEquiv (n : ℤ) :
    CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj
        (complex R P Q)) I n ≃+
      CochainComplex.HomComplex.Cochain
          ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P) HI n where
  toFun := curryCochain R P Q I n
  invFun := uncurryCochain R P Q I n
  left_inv := uncurry_curry R P Q I n
  right_inv := curry_uncurry R P Q I n
  map_add' := curryCochain_add R P Q I n

end ChainComplex.BalancedTensor
