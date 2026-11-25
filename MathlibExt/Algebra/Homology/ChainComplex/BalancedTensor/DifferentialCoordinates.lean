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

public import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor.InverseLaws

/-!
# Integer differential coordinates for tensor–Hom currying

The formulas evaluate the differentials on tensor generators and
full-product coordinates in every integer degree, retaining the
precomposition and postcomposition maps.
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

private theorem d_mk_adjacent (p p' q q' s t : ℤ)
    (hp : p' + 1 = p) (hq : q' + 1 = q) (ht : t + 1 = s) (h : p + q = s)
    (x : P.X p) (y : Q.X q) :
    ((complex R P Q).d s t).hom (mk R P Q p q s h x y) =
      mk R P Q p' q t (by omega) ((P.d p p').hom x) y +
        p.negOnePow • mk R P Q p q' t (by omega) x ((Q.d q q').hom y) := by
  have hp' : p' = p - 1 := by omega
  have hq' : q' = q - 1 := by omega
  have ht' : t = s - 1 := by omega
  subst p' q' t
  exact d_mk R P Q p q s h x y

/-- The original tensor-total Hom differential, evaluated on its two original factors. -/
theorem tensorHom_d_mk (n : ℤ)
    (f : CochainComplex.HomComplex.Cochain
        ((cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj (complex R P Q)) I n)
    (a c d : ℤ) (h : a + c + (n + 1) = d)
    (x : P.X (-a)) (y : Q.X (-c)) :
    ((((homCochainComplex (complex R P Q) I).d n (n + 1)).hom f).v
        (a + c) d h).hom (mk R P Q (-a) (-c) (-(a + c)) (by omega) x y) =
      (f.v (a + c + 1) d (by omega)).hom
        (mk R P Q (-(a + 1)) (-c) (-(a + c + 1)) (by omega)
          ((P.d (-a) (-(a + 1))).hom x) y) +
      (-a).negOnePow • (f.v (a + c + 1) d (by omega)).hom
        (mk R P Q (-a) (-(c + 1)) (-(a + c + 1)) (by omega) x
          ((Q.d (-c) (-(c + 1))).hom y)) +
      (n + 1).negOnePow • (I.d (d - 1) d).hom
        ((f.v (a + c) (d - 1) (by omega)).hom
          (mk R P Q (-a) (-c) (-(a + c)) (by omega) x y)) := by
  let C : CochainComplex AddCommGrpCat.{v} ℤ :=
    (cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj (complex R P Q)
  let S₀ : AddCommGrpCat.{v} := C.X (a + c)
  let S₁ : AddCommGrpCat.{v} := C.X (a + c + 1)
  let z : S₀ := mk R P Q (-a) (-c) (-(a + c)) (by omega) x y
  let z₁ : S₁ := mk R P Q (-(a + 1)) (-c) (-(a + c + 1)) (by omega)
    ((P.d (-a) (-(a + 1))).hom x) y
  let z₂ : S₁ := mk R P Q (-a) (-(c + 1)) (-(a + c + 1)) (by omega) x
    ((Q.d (-c) (-(c + 1))).hom y)
  let dA : S₀ ⟶ S₁ := C.d (a + c) (a + c + 1)
  let dRaw : S₀ ⟶ S₁ := (complex R P Q).d (-(a + c)) (-(a + c + 1))
  have hReindex : dA = dRaw := rfl
  have hRaw : dRaw.hom z = z₁ + (-a).negOnePow • z₂ :=
    d_mk_adjacent R P Q (-a) (-(a + 1)) (-c) (-(c + 1))
      (-(a + c)) (-(a + c + 1)) (by omega) (by omega) (by omega) (by omega) x y
  have hDegree : dA.hom z = z₁ + (-a).negOnePow • z₂ :=
    (congrArg (fun m : S₀ ⟶ S₁ => m.hom z) hReindex).trans hRaw
  let r : S₁ ⟶ I.X d := f.v (a + c + 1) d (by omega)
  let s : S₀ ⟶ I.X (d - 1) := f.v (a + c) (d - 1) (by omega)
  let j : I.X (d - 1) ⟶ I.X d := I.d (d - 1) d
  have hFactorSign : r.hom ((-a).negOnePow • z₂) = (-a).negOnePow • r.hom z₂ :=
    map_zsmul r.hom ((-a).negOnePow : ℤ) z₂
  have hFactor : r.hom (dA.hom z) = r.hom z₁ + (-a).negOnePow • r.hom z₂ :=
    (congrArg r.hom hDegree).trans
      ((r.hom.map_add z₁ ((-a).negOnePow • z₂)).trans
        (congrArg (fun t : I.X d => r.hom z₁ + t) hFactorSign))
  let l : S₀ ⟶ I.X d := dA ≫ r
  let t : S₀ ⟶ I.X d := s ≫ j
  let δf : S₀ ⟶ I.X d :=
    (((homCochainComplex (complex R P Q) I).d n (n + 1)).hom f).v (a + c) d h
  have hDifferential : δf = l + (n + 1).negOnePow • t :=
    homCochainComplex_d_v (complex R P Q) I n (n + 1) rfl f (a + c) d h
  have hLeft : l.hom z = r.hom (dA.hom z) :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_comp dA r) z).trans
      (AddMonoidHom.comp_apply r.hom dA.hom z)
  have hRight : t.hom z = j.hom (s.hom z) :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_comp s j) z).trans
      (AddMonoidHom.comp_apply j.hom s.hom z)
  have hScalar : ((n + 1).negOnePow • t).hom z =
      (n + 1).negOnePow • t.hom z :=
    (DFunLike.congr_fun
      (AddCommGrpCat.hom_zsmul ((n + 1).negOnePow : ℤ) t) z).trans
        (AddMonoidHom.zsmul_apply t.hom ((n + 1).negOnePow : ℤ) z)
  have hSum : (l + (n + 1).negOnePow • t).hom z =
      l.hom z + (n + 1).negOnePow • t.hom z :=
    ((DFunLike.congr_fun (AddCommGrpCat.hom_add l ((n + 1).negOnePow • t)) z).trans
      (AddMonoidHom.add_apply l.hom ((n + 1).negOnePow • t).hom z)).trans
        (congrArg (fun v : I.X d => l.hom z + v) hScalar)
  have hValue := (congrArg (fun m : S₀ ⟶ I.X d => m.hom z) hDifferential).trans
    (hSum.trans (congrArg₂
      (fun v w : I.X d => v + (n + 1).negOnePow • w) hLeft hRight))
  change δf.hom z = r.hom z₁ + (-a).negOnePow • r.hom z₂ +
    (n + 1).negOnePow • j.hom (s.hom z)
  exact hValue.trans (congrArg
    (fun v : I.X d => v + (n + 1).negOnePow • j.hom (s.hom z)) hFactor)

/-- The original nested full-product Hom differential on every pair of source degrees. -/
theorem nestedHom_d_v (n : ℤ)
    (g : CochainComplex.HomComplex.Cochain
        ((cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P) HI n)
    (a b : ℤ) (hab : a + (n + 1) = b)
    (c d : ℤ) (hcd : c + b = d)
    (x : P.X (-a)) (y : Q.X (-c)) :
    ((((((homCochainComplex P HI).d n (n + 1)).hom g).v a b hab).hom x).v
        c d hcd).hom y =
      (((g.v (a + 1) b (by omega)).hom
        ((P.d (-a) (-(a + 1))).hom x)).v c d hcd).hom y +
      (n + 1).negOnePow •
        ((((g.v a (b - 1) (by omega)).hom x).v (c + 1) d (by omega)).hom
          ((Q.d (-c) (-(c + 1))).hom y) +
        b.negOnePow • (I.d (d - 1) d).hom
          ((((g.v a (b - 1) (by omega)).hom x).v c (d - 1) (by omega)).hom y)) := by
  let := homCochainModule R Q I b
  let := homCochainModule R Q I (b - 1)
  let CP : CochainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ :=
    (cochainComplexEquivalence (ModuleCat.{v} Rᵐᵒᵖ)).functor.obj P
  let H : CochainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ := moduleHomCochainComplex R Q I
  let A₀ : ModuleCat.{v} Rᵐᵒᵖ := CP.X a
  let A₁ : ModuleCat.{v} Rᵐᵒᵖ := CP.X (a + 1)
  let B₀ : ModuleCat.{v} Rᵐᵒᵖ := H.X (b - 1)
  let B₁ : ModuleCat.{v} Rᵐᵒᵖ := H.X b
  let dP : A₀ ⟶ A₁ := CP.d a (a + 1)
  let dP₀ : A₀ ⟶ A₁ := P.d (-a) (-(a + 1))
  have hPReindex : dP = dP₀ := rfl
  have hPValue : dP.hom x = dP₀.hom x :=
    congrArg (fun m : A₀ ⟶ A₁ => m.hom x) hPReindex
  let r : A₁ ⟶ B₁ := g.v (a + 1) b (by omega)
  let s : A₀ ⟶ B₀ := g.v a (b - 1) (by omega)
  let j : B₀ ⟶ B₁ := H.d (b - 1) b
  let z : B₀ := s.hom x
  let l : A₀ ⟶ B₁ := dP ≫ r
  let t : A₀ ⟶ B₁ := s ≫ j
  let δg : A₀ ⟶ B₁ :=
    (((homCochainComplex P H).d n (n + 1)).hom g).v a b hab
  have hDifferential : δg = l + (n + 1).negOnePow • t :=
    homCochainComplex_d_v P H n (n + 1) rfl g a b hab
  have hLeft : l.hom x = r.hom (dP₀.hom x) :=
    ((DFunLike.congr_fun (ModuleCat.hom_comp dP r) x).trans
      (LinearMap.comp_apply r.hom dP.hom x)).trans (congrArg r.hom hPValue)
  have hRight : t.hom x = j.hom z :=
    (DFunLike.congr_fun (ModuleCat.hom_comp s j) x).trans
      (LinearMap.comp_apply j.hom s.hom x)
  have hScalar : ((n + 1).negOnePow • t).hom x =
      (n + 1).negOnePow • t.hom x :=
    (DFunLike.congr_fun
      (ModuleCat.hom_zsmul ((n + 1).negOnePow : ℤ) t) x).trans
        (LinearMap.smul_apply ((n + 1).negOnePow : ℤ) t.hom x)
  have hSum : (l + (n + 1).negOnePow • t).hom x =
      l.hom x + (n + 1).negOnePow • t.hom x :=
    ((DFunLike.congr_fun (ModuleCat.hom_add l ((n + 1).negOnePow • t)) x).trans
      (LinearMap.add_apply l.hom ((n + 1).negOnePow • t).hom x)).trans
        (congrArg (fun v : B₁ => l.hom x + v) hScalar)
  have hOuterValue : δg.hom x = r.hom (dP₀.hom x) +
      (n + 1).negOnePow • j.hom z :=
    (congrArg (fun m : A₀ ⟶ B₁ => m.hom x) hDifferential).trans
      (hSum.trans (congrArg₂
        (fun v w : B₁ => v + (n + 1).negOnePow • w) hLeft hRight))
  let CQ : CochainComplex AddCommGrpCat.{v} ℤ := moduleHomDomainCochain R Q
  let C₀ : AddCommGrpCat.{v} := CQ.X c
  let C₁ : AddCommGrpCat.{v} := CQ.X (c + 1)
  let dQ : C₀ ⟶ C₁ := CQ.d c (c + 1)
  let dQ₀ : C₀ ⟶ C₁ :=
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).map (Q.d (-c) (-(c + 1)))
  have hQReindex : dQ = dQ₀ := rfl
  have hQRawValue : dQ₀.hom y = (Q.d (-c) (-(c + 1))).hom y := rfl
  have hQValue : dQ.hom y = (Q.d (-c) (-(c + 1))).hom y :=
    (congrArg (fun m : C₀ ⟶ C₁ => m.hom y) hQReindex).trans hQRawValue
  let u : C₁ ⟶ I.X d := z.v (c + 1) d (by omega)
  let v : C₀ ⟶ I.X (d - 1) := z.v c (d - 1) (by omega)
  let k : I.X (d - 1) ⟶ I.X d := I.d (d - 1) d
  let lI : C₀ ⟶ I.X d := dQ ≫ u
  let tI : C₀ ⟶ I.X d := v ≫ k
  let δz : C₀ ⟶ I.X d := (j.hom z).v c d hcd
  have hInnerDifferential : δz = lI + b.negOnePow • tI := by
    have he := moduleHomCochainComplex_d_apply R Q I (b - 1) b z
    have hv := congrArg (fun w : CochainComplex.HomComplex.Cochain
      (moduleHomDomainCochain R Q) I b => w.v c d hcd) he
    exact hv.trans (homCochainComplex_d_v
      (moduleHomUnderlyingChain R Q) I (b - 1) b (by omega) z c d hcd)
  have hInnerLeft : lI.hom y = u.hom ((Q.d (-c) (-(c + 1))).hom y) :=
    ((DFunLike.congr_fun (AddCommGrpCat.hom_comp dQ u) y).trans
      (AddMonoidHom.comp_apply u.hom dQ.hom y)).trans (congrArg u.hom hQValue)
  have hInnerRight : tI.hom y = k.hom (v.hom y) :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_comp v k) y).trans
      (AddMonoidHom.comp_apply k.hom v.hom y)
  have hInnerScalar : (b.negOnePow • tI).hom y = b.negOnePow • tI.hom y :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_zsmul (b.negOnePow : ℤ) tI) y).trans
      (AddMonoidHom.zsmul_apply tI.hom (b.negOnePow : ℤ) y)
  have hInnerSum : (lI + b.negOnePow • tI).hom y =
      lI.hom y + b.negOnePow • tI.hom y :=
    ((DFunLike.congr_fun (AddCommGrpCat.hom_add lI (b.negOnePow • tI)) y).trans
      (AddMonoidHom.add_apply lI.hom (b.negOnePow • tI).hom y)).trans
        (congrArg (fun w : I.X d => lI.hom y + w) hInnerScalar)
  have hInnerValue : δz.hom y = u.hom ((Q.d (-c) (-(c + 1))).hom y) +
      b.negOnePow • k.hom (v.hom y) :=
    (congrArg (fun m : C₀ ⟶ I.X d => m.hom y) hInnerDifferential).trans
      (hInnerSum.trans (congrArg₂
        (fun w w' : I.X d => w + b.negOnePow • w') hInnerLeft hInnerRight))
  let w₁ : CochainComplex.HomComplex.Cochain CQ I b := r.hom (dP₀.hom x)
  let w₂ : CochainComplex.HomComplex.Cochain CQ I b := j.hom z
  have hComponent : (w₁ + (n + 1).negOnePow • w₂).v c d hcd =
      w₁.v c d hcd + (n + 1).negOnePow • w₂.v c d hcd :=
    (CochainComplex.HomComplex.Cochain.add_v
      w₁ ((n + 1).negOnePow • w₂) c d hcd).trans
        (congrArg (fun m : C₀ ⟶ I.X d => w₁.v c d hcd + m)
          (CochainComplex.HomComplex.Cochain.units_smul_v (R := ℤ)
            (n + 1).negOnePow w₂ c d hcd))
  have hComponentScalar : ((n + 1).negOnePow • w₂.v c d hcd).hom y =
      (n + 1).negOnePow • (w₂.v c d hcd).hom y :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_zsmul
      ((n + 1).negOnePow : ℤ) (w₂.v c d hcd)) y).trans
        (AddMonoidHom.zsmul_apply (w₂.v c d hcd).hom ((n + 1).negOnePow : ℤ) y)
  have hComponentValue : ((w₁ + (n + 1).negOnePow • w₂).v c d hcd).hom y =
      (w₁.v c d hcd).hom y + (n + 1).negOnePow • (w₂.v c d hcd).hom y :=
    (congrArg (fun m : C₀ ⟶ I.X d => m.hom y) hComponent).trans
      (((DFunLike.congr_fun (AddCommGrpCat.hom_add
        (w₁.v c d hcd) ((n + 1).negOnePow • w₂.v c d hcd)) y).trans
          (AddMonoidHom.add_apply (w₁.v c d hcd).hom
            ((n + 1).negOnePow • w₂.v c d hcd).hom y)).trans
              (congrArg (fun w : I.X d => (w₁.v c d hcd).hom y + w) hComponentScalar))
  have hOuterPoint := (congrArg (fun w : CochainComplex.HomComplex.Cochain CQ I b =>
    (w.v c d hcd).hom y) hOuterValue).trans hComponentValue
  change (((δg.hom x).v c d hcd).hom y) = (w₁.v c d hcd).hom y +
    (n + 1).negOnePow • (u.hom ((Q.d (-c) (-(c + 1))).hom y) +
      b.negOnePow • k.hom (v.hom y))
  exact hOuterPoint.trans (congrArg
    (fun w : I.X d => (w₁.v c d hcd).hom y + (n + 1).negOnePow • w) hInnerValue)

end ChainComplex.BalancedTensor
