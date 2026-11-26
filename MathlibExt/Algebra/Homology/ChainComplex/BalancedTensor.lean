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

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.Grp.Colimits
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.Bifunctor
public import MathlibExt.Algebra.Homology.TensorSignsDownInt
public meta import Lean.Elab.Tactic.Omega

/-!
# Balanced tensor totals of integer chain complexes

Let `R` be an associative ring, `P` an integer chain complex of right `R`-modules, and `Q` an
integer chain complex of left `R`-modules. The tensor total has degree-`n` object the direct
sum of the balanced tensor groups `P_p ⊗_R Q_q` over all integer pairs `p + q = n`.

The inclusion of a pure class is bilinear and balanced. Its differential is `d_P x ⊗ y +
(-1)^p x ⊗ d_Q y`, in the summands `(p - 1, q)` and `(p, q - 1)`. Chain maps in the factors
act on these classes factorwise. The complexes may be unbounded, and their common carrier
universe is independent of the ring universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace ChainComplex.BalancedTensor

universe u v

variable (R : Type u) [Ring R]

/-- Integer chain balanced tensor as a total-complex bifunctor.

Extend the group-valued balanced tensor bifunctor to integer chain bicomplexes and take the
direct-sum total. This gives a bifunctor from right and left `R`-module chain complexes to
additive-group chain complexes. -/
def bifunctor :
    ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ ⥤
      ChainComplex (ModuleCat.{v} R) ℤ ⥤ ChainComplex AddCommGrpCat.{v} ℤ := by
  letI : ∀ (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
      (Q : ChainComplex (ModuleCat.{v} R) ℤ),
      HomologicalComplex.HasMapBifunctor P Q (ModuleCat.BalancedTensor.groupBifunctor R)
        (ComplexShape.down ℤ) := fun P Q => by
    intro n
    infer_instance
  exact (ModuleCat.BalancedTensor.groupBifunctor R).map₂HomologicalComplex
    (ComplexShape.down ℤ) (ComplexShape.down ℤ) (ComplexShape.down ℤ)

/-- Direct-sum balanced tensor total of two integer chain complexes.

For a right-module complex `P` and left-module complex `Q`, `complex R P Q` is the homological
tensor total, with degree-`n` sum over all `p + q = n`. -/
def complex (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) : ChainComplex AddCommGrpCat.{v} ℤ :=
  ((bifunctor R).obj P).obj Q

/-- Pure balanced tensor in an integer total degree.

For integers `p`, `q`, and `n` with `p + q = n`, include `[x ⊗ y]`, where `x : P.X p` and `y :
Q.X q`, in the corresponding summand of `(complex R P Q).X n`. -/
def mk (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (x : P.X p) (y : Q.X q) : (complex R P Q).X n := by
  letI : Module ℤ (Q.X q) := Module.compHom (Q.X q) (algebraMap ℤ R)
  exact (HomologicalComplex.ιMapBifunctor P Q (ModuleCat.BalancedTensor.groupBifunctor R)
    (ComplexShape.down ℤ) p q n h).hom
      (TensorProduct.Balanced.mk ℤ R (P.X p) (Q.X q) x y)

/-- Tensor-total pure class is additive in the right-module element.

For fixed total-degree indices and `y`, the total class of `(x + x') ⊗ y` equals the sum of
the classes of `x ⊗ y` and `x' ⊗ y`. -/
theorem mk_add_left (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (x x' : P.X p) (y : Q.X q) :
    mk R P Q p q n h (x + x') y = mk R P Q p q n h x y + mk R P Q p q n h x' y := by
  let : Module ℤ (Q.X q) := Module.compHom (Q.X q) (algebraMap ℤ R)
  let A : AddCommGrpCat.{v} :=
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.X p)).obj (Q.X q)
  let ι : A ⟶ (complex R P Q).X n := HomologicalComplex.ιMapBifunctor P Q
    (ModuleCat.BalancedTensor.groupBifunctor R) (ComplexShape.down ℤ) p q n h
  let μ := TensorProduct.Balanced.mk ℤ R (P.X p) (Q.X q)
  let a : A := μ x y
  let a' : A := μ x' y
  let aSum : A := μ (x + x') y
  have hPoint : aSum = a + a' := by
    exact (DFunLike.congr_fun (μ.map_add x x') y).trans
      (LinearMap.add_apply (μ x) (μ x') y)
  exact (congrArg ι.hom hPoint).trans (ι.hom.map_add a a')

/-- Tensor-total pure class is additive in the left-module element.

For fixed total-degree indices and `x`, the total class of `x ⊗ (y + y')` equals the sum of
the classes of `x ⊗ y` and `x ⊗ y'`. -/
theorem mk_add_right (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (x : P.X p) (y y' : Q.X q) :
    mk R P Q p q n h x (y + y') = mk R P Q p q n h x y + mk R P Q p q n h x y' := by
  let : Module ℤ (Q.X q) := Module.compHom (Q.X q) (algebraMap ℤ R)
  let A : AddCommGrpCat.{v} :=
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (P.X p)).obj (Q.X q)
  let ι : A ⟶ (complex R P Q).X n := HomologicalComplex.ιMapBifunctor P Q
    (ModuleCat.BalancedTensor.groupBifunctor R) (ComplexShape.down ℤ) p q n h
  let μ := TensorProduct.Balanced.mk ℤ R (P.X p) (Q.X q)
  let a : A := μ x y
  let a' : A := μ x y'
  let aSum : A := μ x (y + y')
  have hPoint : aSum = a + a' := by
    exact (μ x).map_add y y'
  exact (congrArg ι.hom hPoint).trans (ι.hom.map_add a a')

/-- Tensor-total pure classes satisfy the R-balancing relation.

For `r : R`, the total classes represented by `(op r • x) ⊗ y` and `x ⊗ (r • y)` are equal in
the same degree `p + q`. -/
theorem mk_balance (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (r : R) (x : P.X p) (y : Q.X q) :
    mk R P Q p q n h (MulOpposite.op r • x) y = mk R P Q p q n h x (r • y) := by
  let : Module ℤ (Q.X q) := Module.compHom (Q.X q) (algebraMap ℤ R)
  exact congrArg (HomologicalComplex.ιMapBifunctor P Q
      (ModuleCat.BalancedTensor.groupBifunctor R) (ComplexShape.down ℤ) p q n h).hom
    (TensorProduct.Balanced.balance ℤ R (P.X p) (Q.X q) r x y)

/-- Integer tensor-total differential on a pure balanced class.

For `p + q = n`, the differential from total degree `n` to `n - 1` sends `[x ⊗ y]` to the
class of `d_P x ⊗ y` in `(p - 1, q)` plus `p.negOnePow` times the class of `x ⊗ d_Q y` in `(p,
q - 1)`. -/
theorem d_mk (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (x : P.X p) (y : Q.X q) :
    ((complex R P Q).d n (n - 1)).hom (mk R P Q p q n h x y) =
      mk R P Q (p - 1) q (n - 1) (by omega) ((P.d p (p - 1)).hom x) y +
        p.negOnePow • mk R P Q p (q - 1) (n - 1) (by omega) x
          ((Q.d q (q - 1)).hom y) := by
  let : Module ℤ (Q.X q) := Module.compHom (Q.X q) (algebraMap ℤ R)
  let : Module ℤ (Q.X (q - 1)) := Module.compHom (Q.X (q - 1)) (algebraMap ℤ R)
  let F := ModuleCat.BalancedTensor.groupBifunctor R
  have hι :
      HomologicalComplex.ιMapBifunctor P Q F (ComplexShape.down ℤ) p q n h ≫
        (complex R P Q).d n (n - 1) =
      (F.map (P.d p (p - 1))).app (Q.X q) ≫
          HomologicalComplex.ιMapBifunctor P Q F (ComplexShape.down ℤ)
            (p - 1) q (n - 1) (by change p - 1 + q = n - 1; omega) +
        p.negOnePow • ((F.obj (P.X p)).map (Q.d q (q - 1)) ≫
          HomologicalComplex.ιMapBifunctor P Q F (ComplexShape.down ℤ)
            p (q - 1) (n - 1) (by change p + (q - 1) = n - 1; omega)) := by
    change HomologicalComplex.ιMapBifunctor P Q F (ComplexShape.down ℤ) p q n h ≫
      (HomologicalComplex.mapBifunctor P Q F (ComplexShape.down ℤ)).d n (n - 1) = _
    rw [HomologicalComplex.mapBifunctor.d_eq P Q F (ComplexShape.down ℤ) n (n - 1),
      Preadditive.comp_add _ _ _,
      HomologicalComplex.mapBifunctor.ι_D₁ P Q F (ComplexShape.down ℤ)
        n (n - 1) p q h,
      HomologicalComplex.mapBifunctor.ι_D₂ P Q F (ComplexShape.down ℤ)
        n (n - 1) p q h,
      HomologicalComplex.mapBifunctor.d₁_eq P Q F (ComplexShape.down ℤ)
        (by change p - 1 + 1 = p; omega) q (n - 1)
        (by change p - 1 + q = n - 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq P Q F (ComplexShape.down ℤ)
        p (by change q - 1 + 1 = q; omega) (n - 1)
        (by change p + (q - 1) = n - 1; omega)]
    change 1 • ((F.map (P.d p (p - 1))).app (Q.X q) ≫
        HomologicalComplex.ιMapBifunctor P Q F (ComplexShape.down ℤ)
          (p - 1) q (n - 1) (by change p - 1 + q = n - 1; omega)) +
      p.negOnePow • ((F.obj (P.X p)).map (Q.d q (q - 1)) ≫
        HomologicalComplex.ιMapBifunctor P Q F (ComplexShape.down ℤ)
          p (q - 1) (n - 1) (by change p + (q - 1) = n - 1; omega)) = _
    rw [one_smul]
  let A : AddCommGrpCat.{v} := (F.obj (P.X p)).obj (Q.X q)
  let A₁ : AddCommGrpCat.{v} := (F.obj (P.X (p - 1))).obj (Q.X q)
  let A₂ : AddCommGrpCat.{v} := (F.obj (P.X p)).obj (Q.X (q - 1))
  let T : AddCommGrpCat.{v} := (complex R P Q).X (n - 1)
  let z : A := TensorProduct.Balanced.mk ℤ R (P.X p) (Q.X q) x y
  let z₁ : A₁ := TensorProduct.Balanced.mk ℤ R (P.X (p - 1)) (Q.X q)
    ((P.d p (p - 1)).hom x) y
  let z₂ : A₂ := TensorProduct.Balanced.mk ℤ R (P.X p) (Q.X (q - 1)) x
    ((Q.d q (q - 1)).hom y)
  let i : A ⟶ (complex R P Q).X n :=
    HomologicalComplex.ιMapBifunctor P Q F (ComplexShape.down ℤ) p q n h
  let i₁ : A₁ ⟶ T := HomologicalComplex.ιMapBifunctor P Q F (ComplexShape.down ℤ)
    (p - 1) q (n - 1) (by change p - 1 + q = n - 1; omega)
  let i₂ : A₂ ⟶ T := HomologicalComplex.ιMapBifunctor P Q F (ComplexShape.down ℤ)
    p (q - 1) (n - 1) (by change p + (q - 1) = n - 1; omega)
  let a : A ⟶ A₁ := (F.map (P.d p (p - 1))).app (Q.X q)
  let b : A ⟶ A₂ := (F.obj (P.X p)).map (Q.d q (q - 1))
  let d : (complex R P Q).X n ⟶ T := (complex R P Q).d n (n - 1)
  let ℓ : A ⟶ T := a ≫ i₁
  let r : A ⟶ T := b ≫ i₂
  have hLeftPoint : a.hom z = z₁ :=
    ModuleCat.BalancedTensor.groupBifunctor_map_mk R (P.d p (p - 1)) (Q.X q) x y
  have hRightPoint : b.hom z = z₂ :=
    ModuleCat.BalancedTensor.groupBifunctor_obj_map_mk R (P.X p) (Q.d q (q - 1)) x y
  have hValue : (i ≫ d).hom z = (ℓ + p.negOnePow • r).hom z :=
    congrArg (fun f : A ⟶ T => f.hom z) hι
  have hSource : (i ≫ d).hom z = d.hom (i.hom z) :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_comp i d) z).trans
      (AddMonoidHom.comp_apply d.hom i.hom z)
  have hLeft : ℓ.hom z = i₁.hom z₁ :=
    ((DFunLike.congr_fun (AddCommGrpCat.hom_comp a i₁) z).trans
      (AddMonoidHom.comp_apply i₁.hom a.hom z)).trans (congrArg i₁.hom hLeftPoint)
  have hRight : r.hom z = i₂.hom z₂ :=
    ((DFunLike.congr_fun (AddCommGrpCat.hom_comp b i₂) z).trans
      (AddMonoidHom.comp_apply i₂.hom b.hom z)).trans (congrArg i₂.hom hRightPoint)
  have hScalar : (p.negOnePow • r).hom z = p.negOnePow • r.hom z :=
    (DFunLike.congr_fun
      (AddCommGrpCat.hom_zsmul (p.negOnePow : ℤ) r) z).trans
        (AddMonoidHom.zsmul_apply r.hom (p.negOnePow : ℤ) z)
  have hSum : (ℓ + p.negOnePow • r).hom z =
      ℓ.hom z + p.negOnePow • r.hom z :=
    ((DFunLike.congr_fun (AddCommGrpCat.hom_add ℓ (p.negOnePow • r)) z).trans
      (AddMonoidHom.add_apply ℓ.hom (p.negOnePow • r).hom z)).trans
        (congrArg (fun t : T => ℓ.hom z + t) hScalar)
  change d.hom (i.hom z) = i₁.hom z₁ + p.negOnePow • i₂.hom z₂
  exact hSource.symm.trans (hValue.trans (hSum.trans
    (congrArg₂ (fun x y : T => x + p.negOnePow • y) hLeft hRight)))

/-- Chain map induced on a balanced tensor total.

Chain maps `f : P ⟶ P'` and `g : Q ⟶ Q'` induce a chain map `complex R P Q ⟶ complex R P' Q'`
by the two-variable tensor map. -/
def map {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q Q' : ChainComplex (ModuleCat.{v} R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    complex R P Q ⟶ complex R P' Q' :=
  HomologicalComplex.mapBifunctorMap f g (ModuleCat.BalancedTensor.groupBifunctor R)
    (ComplexShape.down ℤ)

/-- Balanced tensor-total map on pure classes.

For `p + q = n`, the degree-`n` map induced by `f` and `g` sends the total class of `x ⊗ y` to
the total class of `(f.f p) x ⊗ (g.f q) y`. -/
theorem map_mk {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q Q' : ChainComplex (ModuleCat.{v} R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q')
    (p q n : ℤ) (h : p + q = n) (x : P.X p) (y : Q.X q) :
    ((map R f g).f n).hom (mk R P Q p q n h x y) =
      mk R P' Q' p q n h ((f.f p).hom x) ((g.f q).hom y) := by
  let : Module ℤ (Q.X q) := Module.compHom (Q.X q) (algebraMap ℤ R)
  let : Module ℤ (Q'.X q) := Module.compHom (Q'.X q) (algebraMap ℤ R)
  let F := ModuleCat.BalancedTensor.groupBifunctor R
  let A₀ : AddCommGrpCat.{v} := (F.obj (P.X p)).obj (Q.X q)
  let A₁ : AddCommGrpCat.{v} := (F.obj (P'.X p)).obj (Q.X q)
  let A₂ : AddCommGrpCat.{v} := (F.obj (P'.X p)).obj (Q'.X q)
  let T : AddCommGrpCat.{v} := (complex R P' Q').X n
  let z : A₀ := TensorProduct.Balanced.mk ℤ R (P.X p) (Q.X q) x y
  let z₁ : A₁ := TensorProduct.Balanced.mk ℤ R (P'.X p) (Q.X q) ((f.f p).hom x) y
  let z₂ : A₂ := TensorProduct.Balanced.mk ℤ R (P'.X p) (Q'.X q)
    ((f.f p).hom x) ((g.f q).hom y)
  let i : A₀ ⟶ (complex R P Q).X n :=
    HomologicalComplex.ιMapBifunctor P Q F (ComplexShape.down ℤ) p q n h
  let i' : A₂ ⟶ T :=
    HomologicalComplex.ιMapBifunctor P' Q' F (ComplexShape.down ℤ) p q n h
  let a : A₀ ⟶ A₁ := (F.map (f.f p)).app (Q.X q)
  let b : A₁ ⟶ A₂ := (F.obj (P'.X p)).map (g.f q)
  let m : (complex R P Q).X n ⟶ T := (map R f g).f n
  have hι : i ≫ m = a ≫ b ≫ i' :=
    HomologicalComplex.ι_mapBifunctorMap
      (K₁ := P) (K₂ := Q) (L₁ := P') (L₂ := Q') f g F (ComplexShape.down ℤ) p q n h
  have hFirst : a.hom z = z₁ :=
    ModuleCat.BalancedTensor.groupBifunctor_map_mk R (f.f p) (Q.X q) x y
  have hSecond : b.hom z₁ = z₂ :=
    ModuleCat.BalancedTensor.groupBifunctor_obj_map_mk R (P'.X p) (g.f q) ((f.f p).hom x) y
  have hValue := congrArg (fun q : A₀ ⟶ T => q.hom z) hι
  have hLeft : (i ≫ m).hom z = m.hom (i.hom z) :=
    (DFunLike.congr_fun (AddCommGrpCat.hom_comp i m) z).trans
      (AddMonoidHom.comp_apply m.hom i.hom z)
  have hRightFirst : (a ≫ b ≫ i').hom z = (b ≫ i').hom z₁ :=
    ((DFunLike.congr_fun (AddCommGrpCat.hom_comp a (b ≫ i')) z).trans
      (AddMonoidHom.comp_apply (b ≫ i').hom a.hom z)).trans
        (congrArg (b ≫ i').hom hFirst)
  have hRightSecond : (b ≫ i').hom z₁ = i'.hom z₂ :=
    ((DFunLike.congr_fun (AddCommGrpCat.hom_comp b i') z₁).trans
      (AddMonoidHom.comp_apply i'.hom b.hom z₁)).trans (congrArg i'.hom hSecond)
  change m.hom (i.hom z) = i'.hom z₂
  exact hLeft.symm.trans (hValue.trans (hRightFirst.trans hRightSecond))

end ChainComplex.BalancedTensor
