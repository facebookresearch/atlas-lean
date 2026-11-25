/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_exists_weilRestriction_points_equiv.lean`
and
`P2M/Sol/S_Algebra_exists_weilRestriction_points_equiv.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra

open MvPolynomial

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
variable {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)

section coords

variable {T : Type u} [CommRing T] [Algebra A T]

private noncomputable def weilCoord (i : ι) : B ⊗[A] T →ₗ[A] T :=
  _root_.TensorProduct.lift
    { toFun := fun b => (β.repr b i) • (LinearMap.id : T →ₗ[A] T)
      map_add' := fun b b' => by ext t; simp [add_smul]
      map_smul' := fun a b => by ext t; simp [mul_smul] }

private theorem weilCoord_tmul (i : ι) (b : B) (t : T) :
    weilCoord β i (b ⊗ₜ t) = (β.repr b i) • t := by
  simp [weilCoord]

private theorem sum_basis_tmul_weilCoord (z : B ⊗[A] T) :
    ∑ i, β i ⊗ₜ[A] weilCoord β i z = z := by
  induction z using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul b t =>
      simp only [weilCoord_tmul]
      calc ∑ i, β i ⊗ₜ[A] (β.repr b i • t) = ∑ i, (β.repr b i • β i) ⊗ₜ[A] t := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [_root_.TensorProduct.tmul_smul, _root_.TensorProduct.smul_tmul']
        _ = (∑ i, β.repr b i • β i) ⊗ₜ[A] t := by rw [_root_.TensorProduct.sum_tmul]
        _ = b ⊗ₜ t := by rw [β.sum_repr b]
  | add x y hx hy =>
      simp only [map_add, _root_.TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

private theorem weilCoord_sum_basis_tmul (x : ι → T) (i : ι) :
    weilCoord β i (∑ j, β j ⊗ₜ[A] x j) = x i := by
  simp [map_sum, weilCoord_tmul, Module.Basis.repr_self, Finsupp.single_apply]

private theorem ext_weilCoord {z z' : B ⊗[A] T}
    (h : ∀ i, weilCoord β i z = weilCoord β i z') : z = z' := by
  rw [← sum_basis_tmul_weilCoord β z, ← sum_basis_tmul_weilCoord β z']
  simp [h]

private theorem weilCoord_mul (z z' : B ⊗[A] T) (i : ι) :
    weilCoord β i (z * z') =
      ∑ j, ∑ k, β.repr (β j * β k) i • (weilCoord β j z * weilCoord β k z') := by
  conv_lhs => rw [← sum_basis_tmul_weilCoord β z, ← sum_basis_tmul_weilCoord β z']
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, map_sum, weilCoord_tmul]

private theorem weilCoord_smul (b : B) (z : B ⊗[A] T) (i : ι) :
    weilCoord β i (b • z) = ∑ j, β.repr (b * β j) i • weilCoord β j z := by
  conv_lhs => rw [← sum_basis_tmul_weilCoord β z]
  rw [Finset.smul_sum]
  simp_rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [_root_.TensorProduct.smul_tmul', smul_eq_mul, weilCoord_tmul]

private theorem weilCoord_one (i : ι) :
    weilCoord β i (1 : B ⊗[A] T) = algebraMap A T (β.repr 1 i) := by
  rw [Algebra.TensorProduct.one_def, weilCoord_tmul, Algebra.algebraMap_eq_smul_one]

private theorem weilCoord_map {T' : Type u} [CommRing T'] [Algebra A T']
    (u : T →ₐ[A] T') (z : B ⊗[A] T) (i : ι) :
    weilCoord β i ((Algebra.TensorProduct.map (AlgHom.id B B) u) z) =
      u (weilCoord β i z) := by
  induction z using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul b t => simp [Algebra.TensorProduct.map_tmul, weilCoord_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end coords

section points

variable {H : Type u} [CommRing H] [Algebra B H]
variable {T : Type u} [CommRing T] [Algebra A T]

private structure WeilCoords (x : H → ι → T) : Prop where
  add : ∀ h h' i, x (h + h') i = x h i + x h' i
  smul : ∀ (b : B) h i, x (b • h) i = ∑ j, β.repr (b * β j) i • x h j
  mul : ∀ h h' i, x (h * h') i =
    ∑ j, ∑ k, β.repr (β j * β k) i • (x h j * x h' k)
  one : ∀ i, x 1 i = algebraMap A T (β.repr 1 i)

private theorem weilCoords_weilCoord (φ : H →ₐ[B] B ⊗[A] T) :
    WeilCoords β (fun h i => weilCoord β i (φ h)) where
  add h h' i := by simp [map_add]
  smul b h i := by rw [map_smul, weilCoord_smul]
  mul h h' i := by rw [map_mul, weilCoord_mul]
  one i := by rw [map_one, weilCoord_one]

private noncomputable def pointOfWeilCoords (x : H → ι → T)
    (hx : WeilCoords β x) : H →ₐ[B] B ⊗[A] T where
  toFun h := ∑ i, β i ⊗ₜ[A] x h i
  map_one' := by
    apply ext_weilCoord β; intro i
    rw [weilCoord_sum_basis_tmul, hx.one, weilCoord_one]
  map_mul' h h' := by
    apply ext_weilCoord β; intro i
    rw [weilCoord_sum_basis_tmul, hx.mul, weilCoord_mul]
    simp_rw [weilCoord_sum_basis_tmul]
  map_zero' := by
    have h0 : ∀ i, x 0 i = 0 := by
      intro i
      have hadd := hx.add 0 0 i
      rw [add_zero] at hadd
      exact left_eq_add.mp hadd
    simp [h0]
  map_add' h h' := by
    simp [hx.add, _root_.TensorProduct.tmul_add, Finset.sum_add_distrib]
  commutes' b := by
    apply ext_weilCoord β; intro i
    rw [weilCoord_sum_basis_tmul, Algebra.algebraMap_eq_smul_one, hx.smul]
    simp_rw [hx.one]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      show (b ⊗ₜ[A] (1 : T) : B ⊗[A] T) = b • (1 : B ⊗[A] T) by
        rw [Algebra.TensorProduct.one_def, _root_.TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      weilCoord_smul]
    simp_rw [weilCoord_one]

private theorem pointOfWeilCoords_apply (x : H → ι → T) (hx : WeilCoords β x) (h : H) :
    pointOfWeilCoords β x hx h = ∑ i, β i ⊗ₜ[A] x h i :=
  rfl

private theorem weilCoord_pointOfWeilCoords (x : H → ι → T) (hx : WeilCoords β x)
    (h : H) (i : ι) : weilCoord β i (pointOfWeilCoords β x hx h) = x h i := by
  rw [pointOfWeilCoords_apply, weilCoord_sum_basis_tmul]

private theorem pointOfWeilCoords_weilCoord (φ : H →ₐ[B] B ⊗[A] T) :
    pointOfWeilCoords β (fun h i => weilCoord β i (φ h))
      (weilCoords_weilCoord β φ) = φ := by
  apply AlgHom.ext; intro h
  rw [pointOfWeilCoords_apply, sum_basis_tmul_weilCoord]

end points

section representing

variable (H : Type u) [CommRing H] [Algebra B H]

private noncomputable def weilRels : Set (MvPolynomial (H × ι) A) :=
  {r | (∃ (h h' : H) (i : ι), r = X (h + h', i) - X (h, i) - X (h', i)) ∨
       (∃ (b : B) (h : H) (i : ι),
         r = X (b • h, i) - ∑ j, C (β.repr (b * β j) i) * X (h, j)) ∨
       (∃ (h h' : H) (i : ι), r = X (h * h', i) -
         ∑ j, ∑ k, C (β.repr (β j * β k) i) * (X (h, j) * X (h', k))) ∨
       (∃ i : ι, r = X ((1 : H), i) - C (β.repr 1 i))}

private noncomputable def weilRelIdeal : Ideal (MvPolynomial (H × ι) A) := Ideal.span (weilRels β H)

private noncomputable def WeilRes : Type u := MvPolynomial (H × ι) A ⧸ weilRelIdeal β H

private noncomputable instance : CommRing (WeilRes β H) :=
  inferInstanceAs (CommRing (MvPolynomial (H × ι) A ⧸ weilRelIdeal β H))

private noncomputable instance : Algebra A (WeilRes β H) :=
  inferInstanceAs (Algebra A (MvPolynomial (H × ι) A ⧸ weilRelIdeal β H))

variable {H}
variable {T : Type u} [CommRing T] [Algebra A T]

private theorem forall_aeval_weilRels_eq_zero_iff (x : H → ι → T) :
    (∀ r ∈ weilRels β H, aeval (fun p : H × ι => x p.1 p.2) r = 0) ↔ WeilCoords β x := by
  constructor
  · intro hr
    refine ⟨fun h h' i => ?_, fun b h i => ?_, fun h h' i => ?_, fun i => ?_⟩
    · have hr1 := hr _ (Or.inl ⟨h, h', i, rfl⟩)
      simp only [map_sub, aeval_X] at hr1
      rw [sub_sub, sub_eq_zero] at hr1
      exact hr1
    · have hr1 := hr _ (Or.inr (Or.inl ⟨b, h, i, rfl⟩))
      simp only [map_sub, aeval_X, map_sum, map_mul, aeval_C] at hr1
      rw [sub_eq_zero] at hr1
      rw [hr1]
      exact Finset.sum_congr rfl fun j _ => (Algebra.smul_def _ _).symm
    · have hr1 := hr _ (Or.inr (Or.inr (Or.inl ⟨h, h', i, rfl⟩)))
      simp only [map_sub, aeval_X, map_sum, map_mul, aeval_C] at hr1
      rw [sub_eq_zero] at hr1
      rw [hr1]
      exact Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm
    · have hr1 := hr _ (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))
      simp only [map_sub, aeval_X, aeval_C] at hr1
      rw [sub_eq_zero] at hr1
      exact hr1
  · rintro hx r (⟨h, h', i, rfl⟩ | ⟨b, h, i, rfl⟩ | ⟨h, h', i, rfl⟩ | ⟨i, rfl⟩)
    · simp only [map_sub, aeval_X, hx.add]; ring
    · rw [map_sub, aeval_X, hx.smul]
      simp only [map_sum, map_mul, aeval_C, aeval_X, Algebra.smul_def, sub_self]
    · rw [map_sub, aeval_X, hx.mul]
      simp only [map_sum, map_mul, aeval_C, aeval_X, Algebra.smul_def, sub_self]
    · simp only [map_sub, aeval_X, aeval_C, hx.one, sub_self]

private theorem aeval_mem_weilRelIdeal_eq_zero (x : H → ι → T)
    (hx : WeilCoords β x) :
    ∀ r ∈ weilRelIdeal β H, aeval (fun p : H × ι => x p.1 p.2) r = 0 := by
  intro r hr
  have hle : weilRelIdeal β H ≤
      RingHom.ker (aeval (R := A) (fun p : H × ι => x p.1 p.2)) := by
    rw [weilRelIdeal, Ideal.span_le]
    intro r hr
    exact (forall_aeval_weilRels_eq_zero_iff β x).2 hx r hr
  exact hle hr

private noncomputable def weilGen (h : H) (i : ι) : WeilRes β H :=
  Ideal.Quotient.mk (weilRelIdeal β H) (X (h, i))

private theorem mkₐ_X_weil (h : H) (i : ι) :
    Ideal.Quotient.mkₐ A (weilRelIdeal β H) (X (h, i)) = weilGen β h i :=
  rfl

private theorem weilCoords_apply_weilGen (f : WeilRes β H →ₐ[A] T) :
    WeilCoords β (fun h i => f (weilGen β h i)) := by
  rw [← forall_aeval_weilRels_eq_zero_iff]
  intro r hr
  have hfm : (f.comp (Ideal.Quotient.mkₐ A (weilRelIdeal β H))) =
      aeval (fun p : H × ι => f (weilGen β p.1 p.2)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, aeval_X]
    rfl
  have hr0 : (Ideal.Quotient.mkₐ A (weilRelIdeal β H) :
      MvPolynomial (H × ι) A →ₐ[A] WeilRes β H) r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)
  rw [← hfm]
  show f ((Ideal.Quotient.mkₐ A (weilRelIdeal β H) :
    MvPolynomial (H × ι) A →ₐ[A] WeilRes β H) r) = 0
  rw [hr0]
  exact map_zero f

private noncomputable def toWeilPoint (f : WeilRes β H →ₐ[A] T) :
    H →ₐ[B] B ⊗[A] T :=
  pointOfWeilCoords β (fun h i => f (weilGen β h i)) (weilCoords_apply_weilGen β f)

private noncomputable def ofWeilPoint (φ : H →ₐ[B] B ⊗[A] T) :
    WeilRes β H →ₐ[A] T :=
  Ideal.Quotient.liftₐ (weilRelIdeal β H)
    (aeval (fun p : H × ι => weilCoord β p.2 (φ p.1)))
    (aeval_mem_weilRelIdeal_eq_zero β (fun h i => weilCoord β i (φ h))
      (weilCoords_weilCoord β φ))

private theorem ofWeilPoint_weilGen (φ : H →ₐ[B] B ⊗[A] T) (h : H) (i : ι) :
    ofWeilPoint β φ (weilGen β h i) = weilCoord β i (φ h) := by
  unfold ofWeilPoint
  rw [← mkₐ_X_weil]
  have h := AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp (weilRelIdeal β H)
    (aeval (fun p : H × ι => weilCoord β p.2 (φ p.1)))
    (aeval_mem_weilRelIdeal_eq_zero β (fun h i => weilCoord β i (φ h))
      (weilCoords_weilCoord β φ))) (X (h, i))
  rw [AlgHom.comp_apply, aeval_X] at h
  exact h

private theorem toWeilPoint_apply (f : WeilRes β H →ₐ[A] T) (h : H) :
    toWeilPoint β f h = ∑ i, β i ⊗ₜ[A] f (weilGen β h i) :=
  rfl

private theorem pointOfWeilCoords_congr {x x' : H → ι → T}
    (hx : WeilCoords β x) (hx' : WeilCoords β x') (e : x = x') :
    pointOfWeilCoords β x hx = pointOfWeilCoords β x' hx' := by
  subst e; rfl

private noncomputable def weilPointsEquiv :
    (WeilRes β H →ₐ[A] T) ≃ (H →ₐ[B] B ⊗[A] T) where
  toFun := toWeilPoint β
  invFun := ofWeilPoint β
  left_inv f := by
    refine Ideal.Quotient.algHom_ext A ?_
    apply MvPolynomial.algHom_ext
    intro p
    show ofWeilPoint β (toWeilPoint β f)
        (Ideal.Quotient.mkₐ A (weilRelIdeal β H) (X p)) =
      f (Ideal.Quotient.mkₐ A (weilRelIdeal β H) (X p))
    rw [mkₐ_X_weil, ofWeilPoint_weilGen, toWeilPoint, weilCoord_pointOfWeilCoords]
  right_inv φ := by
    change pointOfWeilCoords β _ _ = φ
    rw [pointOfWeilCoords_congr β (weilCoords_apply_weilGen β (ofWeilPoint β φ))
      (weilCoords_weilCoord β φ)
      (funext fun h => funext fun i => ofWeilPoint_weilGen β φ h i)]
    exact pointOfWeilCoords_weilCoord β φ

private theorem weilPointsEquiv_apply (f : WeilRes β H →ₐ[A] T) (h : H) :
    weilPointsEquiv β f h = ∑ i, β i ⊗ₜ[A] f (weilGen β h i) :=
  rfl

private theorem weilPointsEquiv_natural {T' : Type u} [CommRing T'] [Algebra A T']
    (u : T →ₐ[A] T') (f : WeilRes β H →ₐ[A] T) :
    weilPointsEquiv β (u.comp f) =
      (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (weilPointsEquiv β f) := by
  apply AlgHom.ext; intro h
  rw [AlgHom.comp_apply, weilPointsEquiv_apply, weilPointsEquiv_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.map_tmul]; rfl

end representing

/-- Weil restriction along a finite free extension: for `B` finite free over
`A` and a `B`-algebra `H`, there is an `A`-algebra `W` whose `T`-points are
naturally the `B`-algebra maps from `H` to `B ⊗[A] T`. -/
public theorem exists_weilRestriction_points_equiv
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B]
    (H : Type u) [CommRing H] [Algebra B H] :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra A W),
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T],
          (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)),
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T']
          (u : T →ₐ[A] T') (f : W →ₐ[A] T),
          e T' (u.comp f) =
            (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f) := by
  classical
  let ι : Type u := Module.Free.ChooseBasisIndex A B
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype A B
  let β : Module.Basis ι A B := Module.Free.chooseBasis A B
  exact ⟨WeilRes β H, inferInstance, inferInstance, fun T _ _ => weilPointsEquiv β,
    fun T T' _ _ _ _ u f => weilPointsEquiv_natural β u f⟩

end Algebra
