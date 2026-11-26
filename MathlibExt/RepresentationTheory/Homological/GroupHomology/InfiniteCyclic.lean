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

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Oriented first homology of an infinite cyclic group

Let k be a commutative ring and e:G≅*Multiplicative ℤ a chosen
orientation of an infinite cyclic group G. With trivial coefficients k,
H₁(G,k) is k-linearly isomorphic to k.

A degree-one cycle supported at g with coefficient a maps to e(g).toAdd•a.
For a finitely supported cycle f, the value is ∑_g e(g).toAdd•f(g).
The chosen positive generator e⁻¹(1) therefore carries coefficient a
to a. No characteristic assumption on k is needed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option warningAsError true

universe u

open CategoryTheory
open scoped TensorProduct

namespace groupHomology

/-- Let k be a commutative ring, G a group and e:G≅*Multiplicative ℤ
a chosen orientation of the infinite cyclic group. Coefficients are
the trivial representation k_triv.
This is the k-linear isomorphism H₁(G,k_triv)≅k whose
generator convention sends the chosen positive generator with
coefficient a to a. -/
noncomputable def H1IsoOfMulEquivInt
    (k G : Type u) [CommRing k] [Group G]
    (e : G ≃* Multiplicative ℤ) :
    groupHomology (Rep.trivial k G k) 1 ≅ ModuleCat.of k k := by
  let eInt : Additive (Group.Abelianization G) ≃ₗ[ℤ] ℤ :=
    (((e.abelianizationCongr.trans Group.Abelianization.equivOfComm.symm).toAdditive).trans
      (AddEquiv.additiveMultiplicative ℤ)).toIntLinearEquiv
  let E : groupHomology (Rep.trivial k G k) 1 ≃+ k :=
    (H1AddEquivOfIsTrivial (Rep.trivial k G k)).trans
      ((TensorProduct.congr eInt (LinearEquiv.refl ℤ k)).trans
        (TensorProduct.lid ℤ k)).toAddEquiv
  have hsingle (g : G) (a : k) :
      E (H1π (Rep.trivial k G k)
          ((cycles₁IsoOfIsTrivial (Rep.trivial k G k)).inv
            (Finsupp.single g a))) =
        (e g).toAdd • a := by
    dsimp only [E, eInt]
    rw [AddEquiv.trans_apply, H1AddEquivOfIsTrivial_single]
    simp
  have hsmul (c : k) (x : groupHomology (Rep.trivial k G k) 1) :
      E (c • x) = c • E x := by
    induction x using H1_induction_on with
    | h z =>
      let I := cycles₁IsoOfIsTrivial (Rep.trivial k G k)
      have hf : ∀ f : G →₀ k,
          E (H1π (Rep.trivial k G k) (I.inv (c • f))) =
            c • E (H1π (Rep.trivial k G k) (I.inv f)) := by
        intro f
        induction f using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg =>
            simpa only [smul_add, map_add] using congrArg₂ (· + ·) hf hg
        | single g a =>
            rw [Finsupp.smul_single, hsingle, hsingle]
            exact smul_comm (e g).toAdd c a
      simpa only [map_smul, I.hom_inv_id_apply] using hf (I.hom z)
  exact (E.toLinearEquiv hsmul).toModuleIso

/-- Let k be a commutative ring, G a group and e:G≅*Multiplicative ℤ
a chosen orientation of the infinite cyclic group. Coefficients are
the trivial representation k_triv.
The degree-one class supported at g with coefficient a maps to
e(g).toAdd•a, where the scalar is integer multiplication in k. -/
@[simp]
theorem H1IsoOfMulEquivInt_hom_H1π_single
    (k G : Type u) [CommRing k] [Group G]
    (e : G ≃* Multiplicative ℤ) (g : G) (a : k) :
    (H1IsoOfMulEquivInt k G e).hom
        (H1π (Rep.trivial k G k)
          ((cycles₁IsoOfIsTrivial (Rep.trivial k G k)).inv
            (Finsupp.single g a))) =
      (e g).toAdd • a := by
  change ((H1AddEquivOfIsTrivial (Rep.trivial k G k)).trans
      ((TensorProduct.congr
        (((e.abelianizationCongr.trans Group.Abelianization.equivOfComm.symm).toAdditive).trans
          (AddEquiv.additiveMultiplicative ℤ)).toIntLinearEquiv
        (LinearEquiv.refl ℤ k)).trans (TensorProduct.lid ℤ k)).toAddEquiv)
    (H1π (Rep.trivial k G k)
      ((cycles₁IsoOfIsTrivial (Rep.trivial k G k)).inv
        (Finsupp.single g a))) = _
  rw [AddEquiv.trans_apply, H1AddEquivOfIsTrivial_single]
  simp

/-- Let k be a commutative ring, G a group and e:G≅*Multiplicative ℤ
a chosen orientation of the infinite cyclic group. Coefficients are
the trivial representation k_triv.
For a finitely supported cycle f:G→₀k, the oriented H₁
comparison has value ∑_g e(g).toAdd•f(g). -/
@[simp]
theorem H1IsoOfMulEquivInt_hom_H1π
    (k G : Type u) [CommRing k] [Group G]
    (e : G ≃* Multiplicative ℤ) (f : G →₀ k) :
    (H1IsoOfMulEquivInt k G e).hom
        (H1π (Rep.trivial k G k)
          ((cycles₁IsoOfIsTrivial (Rep.trivial k G k)).inv f)) =
      f.sum fun g a => (e g).toAdd • a := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp [H1IsoOfMulEquivInt]
  | add f g hf hg =>
      rw [map_add, map_add, map_add, hf, hg]
      exact (Finsupp.sum_add_index (by simp) (by intros; simp)).symm
  | single g a =>
      simpa using H1IsoOfMulEquivInt_hom_H1π_single k G e g a

/-- Let k be a commutative ring, G a group and e:G≅*Multiplicative ℤ
a chosen orientation of the infinite cyclic group. Coefficients are
the trivial representation k_triv.
The class supported at e⁻¹(Multiplicative.ofAdd(1)) with
coefficient a maps to a. -/
@[simp]
theorem H1IsoOfMulEquivInt_generator
    (k G : Type u) [CommRing k] [Group G]
    (e : G ≃* Multiplicative ℤ) (a : k) :
    (H1IsoOfMulEquivInt k G e).hom
        (H1π (Rep.trivial k G k)
          ((cycles₁IsoOfIsTrivial (Rep.trivial k G k)).inv
            (Finsupp.single (e.symm (Multiplicative.ofAdd 1)) a))) =
      a := by
  simpa using H1IsoOfMulEquivInt_hom_H1π_single k G e
    (e.symm (Multiplicative.ofAdd 1)) a

end groupHomology
