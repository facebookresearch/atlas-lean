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

public import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor.Curry

/-!
# Full-product to tensor-total Hom inverse

Each summand uses underived uncurrying. Negative-reindexing unit maps
identify its two module factors, and coproduct descent assembles all
integer summands without a support assumption on Hom.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace ChainComplex.BalancedTensor

universe u v

variable (R : Type u) [Ring R]
  (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
  (Q : ChainComplex (ModuleCat.{v} R) ℤ)
  (I : CochainComplex AddCommGrpCat.{v} ℤ)

local notation "HI" => moduleHomCochainComplex R Q I

/-- The actual original tensor summand map extracted from a full Hom cochain. -/
def uncurryComponent (n : ℤ) (g : CochainComplex.HomComplex.Cochain
    ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P) HI n)
    (a d : ℤ) (had : a + n = d) (p q : ℤ) (hpq : p + q = -a) :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.X p)).obj (Q.X q) ⟶ I.X d := by
  let b : ℤ := -p + n
  letI := homCochainModule R Q I b
  letI := homGroupModule R (Q.X (-(-q))) (I.X d)
  letI := homGroupModule R (Q.X q) (I.X d)
  let u : P.X p →ₗ[Rᵐᵒᵖ] CochainComplex.HomComplex.Cochain
      (ChainComplex.moduleHomDomainCochain R Q) I b :=
    (g.v (-p) b rfl).hom.comp
      (((cochainComplexEquivalence (ModuleCat Rᵐᵒᵖ)).unitIso.app P).hom.f p).hom
  let v := (homCochainEval R Q I b (-q) d (by dsimp [b]; omega)).comp u
  let w := (ModuleCat.BalancedTensor.homGroupPrecomp R
    (((cochainComplexEquivalence (ModuleCat R)).unitIso.app Q).hom.f q) (I.X d)).comp v
  exact ModuleCat.BalancedTensor.groupUncurry R (P.X p) (Q.X q) (I.X d)
    (Int.triangularSign b • w)

/-- Native total descent assembles every actual tensor summand into the original Hom cochain. -/
def uncurryCochain (n : ℤ) (g : CochainComplex.HomComplex.Cochain
    ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P) HI n) :
    CochainComplex.HomComplex.Cochain ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj
        (complex R P Q)) I n :=
  CochainComplex.HomComplex.Cochain.mk (fun a d had =>
    HomologicalComplex.mapBifunctorDesc (fun p q hpq =>
      uncurryComponent R P Q I n g a d had p q hpq))

/-- The inverse summand map evaluates the original coefficient and the two native unit maps. -/
theorem uncurryComponent_mk (n : ℤ) (g : CochainComplex.HomComplex.Cochain
    ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P) HI n)
    (a d : ℤ) (had : a + n = d) (p q : ℤ) (hpq : p + q = -a)
    (x : P.X p) (y : Q.X q) :
    letI : Module ℤ (Q.X q) := Module.compHom (Q.X q) (algebraMap ℤ R)
    (uncurryComponent R P Q I n g a d had p q hpq).hom
        (TensorProduct.Balanced.mk ℤ R (P.X p) (Q.X q) x y) =
      Int.triangularSign (-p + n) •
        (((g.v (-p) (-p + n) rfl).hom
          ((((cochainComplexEquivalence (ModuleCat Rᵐᵒᵖ)).unitIso.app P).hom.f p).hom x)).v
            (-q) d (by omega)).hom
          ((((cochainComplexEquivalence (ModuleCat R)).unitIso.app Q).hom.f q).hom y) := by
  let : Module ℤ (Q.X q) := Module.compHom (Q.X q) (algebraMap ℤ R)
  let b : ℤ := -p + n
  let := homCochainModule R Q I b
  let := homGroupModule R (Q.X (-(-q))) (I.X d)
  let := homGroupModule R (Q.X q) (I.X d)
  let E := CochainComplex.HomComplex.Cochain (ChainComplex.moduleHomDomainCochain R Q) I b
  let H₀ := (ChainComplex.moduleHomDomainCochain R Q).X (-q) ⟶ I.X d
  let H₁ := (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj (Q.X q) ⟶ I.X d
  let : Module Rᵐᵒᵖ H₀ := homGroupModule R (Q.X (-(-q))) (I.X d)
  let : Module Rᵐᵒᵖ H₁ := homGroupModule R (Q.X q) (I.X d)
  let L_P : P.X p →ₗ[Rᵐᵒᵖ] P.X (-(-p)) :=
    (((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).unitIso.app P).hom.f p).hom
  let G : P.X (-(-p)) →ₗ[Rᵐᵒᵖ] E := (g.v (-p) b rfl).hom
  let u : P.X p →ₗ[Rᵐᵒᵖ] E := G.comp L_P
  let ev : E →ₗ[Rᵐᵒᵖ] H₀ :=
    homCochainEval R Q I b (-q) d (by dsimp [b]; omega)
  let v : P.X p →ₗ[Rᵐᵒᵖ] H₀ := ev.comp u
  let L_Q : Q.X q ⟶ Q.X (-(-q)) :=
    (((cochainComplexEquivalence (ModuleCat.{v} R)).unitIso.app Q).hom.f q)
  let pre : H₀ →ₗ[Rᵐᵒᵖ] H₁ :=
    ModuleCat.BalancedTensor.homGroupPrecomp R L_Q (I.X d)
  let w : P.X p →ₗ[Rᵐᵒᵖ] H₁ := pre.comp v
  let xp : P.X (-(-p)) := L_P x
  let yp : Q.X (-(-q)) := L_Q.hom y
  let z : E := G xp
  let t : H₀ := z.v (-q) d (by dsimp [b]; omega)
  have hU : u x = z := LinearMap.comp_apply G L_P x
  have hV : v x = t :=
    (LinearMap.comp_apply ev u x).trans
      ((congrArg ev hU).trans
        (homCochainEval_apply R Q I b (-q) d (by dsimp [b]; omega) z))
  have hW : (w x).hom y = t.hom yp :=
    (congrArg (fun h : H₁ => h.hom y) (LinearMap.comp_apply pre v x)).trans
      ((congrArg (fun h : H₀ => (pre h).hom y) hV).trans
        (ModuleCat.BalancedTensor.homGroupPrecomp_apply R L_Q (I.X d) t y))
  have hScalar : ((Int.triangularSign b • w) x).hom y =
      Int.triangularSign b • (w x).hom y := by
    have hMap := congrArg (fun h : H₁ => h.hom y)
      (LinearMap.smul_apply (Int.triangularSign b : ℤ) w x)
    have hValue : ((Int.triangularSign b • (w x)).hom) y =
        Int.triangularSign b • (w x).hom y :=
      (DFunLike.congr_fun
        (AddCommGrpCat.hom_zsmul (Int.triangularSign b : ℤ) (w x)) y).trans
          (AddMonoidHom.zsmul_apply (w x).hom (Int.triangularSign b : ℤ) y)
    exact hMap.trans hValue
  have hUncurry := ModuleCat.BalancedTensor.groupUncurry_mk R (P.X p) (Q.X q)
    (I.X d) (Int.triangularSign b • w) x y
  change (ModuleCat.BalancedTensor.groupUncurry R (P.X p) (Q.X q) (I.X d)
    (Int.triangularSign b • w)).hom
      (TensorProduct.Balanced.mk ℤ R (P.X p) (Q.X q) x y) =
        Int.triangularSign b • t.hom yp
  exact hUncurry.trans (hScalar.trans
    (congrArg (fun value : I.X d => Int.triangularSign b • value) hW))

/-- The native coproduct descent keeps that exact inverse value on every integer summand. -/
theorem uncurryCochain_mk (n : ℤ) (g : CochainComplex.HomComplex.Cochain
    ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P) HI n)
    (a d : ℤ) (had : a + n = d) (p q : ℤ) (hpq : p + q = -a)
    (x : P.X p) (y : Q.X q) :
    ((uncurryCochain R P Q I n g).v a d had).hom
        (mk R P Q p q (-a) hpq x y) =
      Int.triangularSign (-p + n) •
        (((g.v (-p) (-p + n) rfl).hom
          ((((cochainComplexEquivalence (ModuleCat Rᵐᵒᵖ)).unitIso.app P).hom.f p).hom x)).v
            (-q) d (by omega)).hom
          ((((cochainComplexEquivalence (ModuleCat R)).unitIso.app Q).hom.f q).hom y) := by
  let : Module ℤ (Q.X q) := Module.compHom (Q.X q) (algebraMap ℤ R)
  let F := ModuleCat.BalancedTensor.groupBifunctor R
  let A : AddCommGrpCat.{v} := (F.obj (P.X p)).obj (Q.X q)
  let T : AddCommGrpCat.{v} := (complex R P Q).X (-a)
  let z : A := TensorProduct.Balanced.mk ℤ R (P.X p) (Q.X q) x y
  let ι : A ⟶ T := HomologicalComplex.ιMapBifunctor P Q F
    (ComplexShape.down ℤ) p q (-a) (by change p + q = -a; exact hpq)
  let D : T ⟶ I.X d := (uncurryCochain R P Q I n g).v a d had
  let C : A ⟶ I.X d := uncurryComponent R P Q I n g a d had p q hpq
  have hι : ι ≫ D = C := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := P) (K₂ := Q) (F := F) (c := ComplexShape.down ℤ) (A := I.X d) (j := -a)
    (fun p q h => uncurryComponent R P Q I n g a d had p q
      (by change p + q = -a at h; exact h))
    p q (by change p + q = -a; exact hpq)
  have hValue := congrArg (fun f : A ⟶ I.X d => f.hom z) hι
  have hCompose : (ι ≫ D).hom z = D.hom (ι.hom z) :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_comp ι D) z).trans
      (AddMonoidHom.comp_apply D.hom ι.hom z)
  have he : ((uncurryCochain R P Q I n g).v a d had).hom
      (mk R P Q p q (-a) hpq x y) = C.hom z := by
    change D.hom (ι.hom z) = C.hom z
    exact hCompose.symm.trans hValue
  exact he.trans (uncurryComponent_mk R P Q I n g a d had p q hpq x y)

end ChainComplex.BalancedTensor
