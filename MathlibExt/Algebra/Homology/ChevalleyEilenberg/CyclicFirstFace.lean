/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CyclicBracketUncurry
public import MathlibExt.LinearAlgebra.Alternating.HeadAntisymmetrization

/-!
# The first-face formula for a full alternating cyclic tensor

For a k-algebra ring A over a commutative ring, let Ω_n(a) be the complete alternating tensor
on n + 1 inputs, written in first-factor coordinates A ⊗[k] TensorPower k n A. Its Connes
projection is the integral full exterior map, and the signed cyclic operator fixes Ω_n(a).

On n + 2 inputs, applying the first regular Hochschild face multiplies the first two ordered
factors. Its projected alternating value is the bracket-tail map obtained by double
uncurrying. Every regular face contributes that same value after its boundary sign (−1)^i and
Connes projection.

Consequently the Connes differential applied to the projected full exterior word is (n + 2)
times its projected first-face value. These are integral identities and use no rational
normalization.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

local notation "Cλ" => ModuleCat.Algebra.Hochschild.NonUnital.connesComplex

/-- Let k be a commutative ring and A a k-algebra ring. Write π_n : A ⊗[k] TensorPower k n A →
Cλ_n for the Connes projection and Ω_n(a) for cyclicFullTensor k A n a. For n : ℕ and a : Fin
(n + 1) → A, Ω_n(a) is (TensorPower.consEquiv k A n).symm applied to the full alternatization
of tprod a. It lies in A ⊗[k] TensorPower k n A. -/
def cyclicFullTensor (n : ℕ) (a : Fin (n + 1) → A) : A ⊗[k] TensorPower k n A :=
  (TensorPower.consEquiv k A n).symm
    ((PiTensorProduct.tprod k).alternatization a)

/-- Let k be a commutative ring and A a k-algebra ring. Write π_n : A ⊗[k] TensorPower k n A →
Cλ_n for the Connes projection and Ω_n(a) for cyclicFullTensor k A n a. For a : Fin (n + 1) →
A, Ω_n(a) = ∑ σ : Perm(Fin(n+1)), sign(σ) • (a_(σ 0) ⊗ tprod(j ↦ a_(σ(j.succ)))). The first
tensor factor is the permuted zero entry and the tail uses the remaining permuted positions. -/
theorem cyclicFullTensor_eq_sum (n : ℕ) (a : Fin (n + 1) → A) :
    cyclicFullTensor k A n a =
      ∑ σ : Equiv.Perm (Fin (n + 1)), σ.sign •
        (a (σ 0) ⊗ₜ[k] PiTensorProduct.tprod k (fun j => a (σ j.succ))) := by
  rw [cyclicFullTensor, MultilinearMap.alternatization_apply, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact (map_zsmul_unit (TensorPower.consEquiv k A n).symm σ.sign
    (PiTensorProduct.tprod k (a ∘ σ))).trans
      (congrArg (fun x => σ.sign • x)
        (TensorPower.consEquiv_symm_tprod k A n (a ∘ σ)))

/-- Let k be a commutative ring and A a k-algebra ring. Write π_n : A ⊗[k] TensorPower k n A →
Cλ_n for the Connes projection and Ω_n(a) for cyclicFullTensor k A n a. For n : ℕ and a : Fin
(n + 1) → A, π_n(Ω_n(a)) = cyclicFullExterior k A n (exteriorPower.ιMulti k (n + 1) a). -/
theorem cyclicFullTensor_projection (n : ℕ) (a : Fin (n + 1) → A) :
    ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n (cyclicFullTensor k A n a) =
      cyclicFullExterior k A n (exteriorPower.ιMulti k (n + 1) a) := by
  rw [cyclicFullTensor_eq_sum, map_sum, cyclicFullExterior_pure]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_zsmul_unit]
  change σ.sign • ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
      (a (σ 0) ⊗ₜ[k] PiTensorProduct.tprod k (fun j => a (σ j.succ))) =
    σ.sign • ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
      ((TensorPower.consEquiv k A n).symm (PiTensorProduct.tprod k (a ∘ σ)))
  exact congrArg (fun x => σ.sign •
    ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n x)
      (TensorPower.consEquiv_symm_tprod k A n (a ∘ σ)).symm

/-- Let k be a commutative ring and A a k-algebra ring. Write π_n : A ⊗[k] TensorPower k n A →
Cλ_n for the Connes projection and Ω_n(a) for cyclicFullTensor k A n a. For n : ℕ,
cyclicFirstProductMultilinear on a : Fin (n + 2) → A is the Connes class of (a₀*a₁) ⊗ a₂ ⊗ … ⊗
a_(n+1). It is obtained from the complete tensor generator, the regular face with index zero,
and π_n. -/
def cyclicFirstProductMultilinear (n : ℕ) :
    MultilinearMap (RingHom.id k) (fun _ : Fin (n + 2) => A) ((Cλ k A).X n) :=
  (ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n).compMultilinearMap
    ((ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n 0).hom.compMultilinearMap
      ((TensorPower.consEquiv k A (n + 1)).symm.toLinearMap.compMultilinearMap
        (PiTensorProduct.tprod k)))

/-- Let k be a commutative ring and A a k-algebra ring. Write π_n : A ⊗[k] TensorPower k n A →
Cλ_n for the Connes projection and Ω_n(a) for cyclicFullTensor k A n a. For n : ℕ, the full
alternatization of cyclicFirstProductMultilinear k A n equals cyclicTailProductUncurry k A n
as alternating maps on Fin (n + 2). The opposite ordered products pair into associative Lie
brackets. -/
theorem cyclicFirstProduct_alternatization (n : ℕ) :
    (cyclicFirstProductMultilinear k A n).alternatization = cyclicTailProductUncurry k A n := by
  let f : A →ₗ[k] A →ₗ[k]
      MultilinearMap (RingHom.id k) (fun _ : Fin n => A) ((Cλ k A).X n) :=
    { toFun := fun x => ((cyclicMultilinear k A n).curryLeft).comp (LinearMap.mul k A x)
      map_add' := by
        intro x y
        ext z a
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mul_apply_apply,
          map_add, LinearMap.add_apply]
      map_smul' := by
        intro c x
        ext z a
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mul_apply_apply,
          map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hf : LinearMap.uncurryLeft
      (((multilinearCurryLeftEquiv (RingHom.id k)
        (fun _ : Fin (n + 1) => A) ((Cλ k A).X n)).symm.toLinearMap).comp f) =
      cyclicFirstProductMultilinear k A n := by
    apply MultilinearMap.ext
    intro a
    change (LinearMap.uncurryLeft (R := k) (M := fun _ : Fin (n + 1) => A)
      (M₂ := (Cλ k A).X n) (f (a 0))) (Fin.tail a) =
      ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
        ((ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n 0).hom
          ((TensorPower.consEquiv k A (n + 1)).symm (PiTensorProduct.tprod k a)))
    rw [LinearMap.uncurryLeft_apply]
    change ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
        ((TensorPower.consEquiv k A n).symm
          (PiTensorProduct.tprod k
            (Fin.cons (a 0 * (Fin.tail a) 0) (Fin.tail (Fin.tail a))))) = _
    rw [TensorPower.consEquiv_symm_tprod, TensorPower.consEquiv_symm_tprod,
      ModuleCat.Algebra.Hochschild.NonUnital.regularFace_first_tprod]
    rfl
  rw [← hf, MultilinearMap.alternatization_uncurryLeft_twice]
  congr 2

/-- Let k be a commutative ring and A a k-algebra ring. Write π_n : A ⊗[k] TensorPower k n A →
Cλ_n for the Connes projection and Ω_n(a) for cyclicFullTensor k A n a. For a : Fin (n + 2) →
A, π_n(regularFace_0(Ω_(n+1)(a))) = cyclicTailProductUncurry k A n a. The face multiplies the
first two tensor factors in their displayed order. -/
theorem cyclicFullTensor_firstFace (n : ℕ) (a : Fin (n + 2) → A) :
    ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
      ((ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n 0).hom
        (cyclicFullTensor k A (n + 1) a)) = cyclicTailProductUncurry k A n a := by
  rw [cyclicFullTensor_eq_sum, map_sum, map_sum]
  simp only [map_zsmul_unit]
  have h := congrArg (fun f => f a) (cyclicFirstProduct_alternatization k A n)
  rw [MultilinearMap.alternatization_apply] at h
  simp only [MultilinearMap.domDomCongr_apply] at h
  have hproduct (b : Fin (n + 2) → A) :
      cyclicFirstProductMultilinear k A n b =
        ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
          ((ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n 0).hom
            (b 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail b))) := by
    change ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
        ((ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n 0).hom
          ((TensorPower.consEquiv k A (n + 1)).symm (PiTensorProduct.tprod k b))) = _
    exact congrArg (fun x => ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
      ((ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n 0).hom x))
        (TensorPower.consEquiv_symm_tprod k A (n + 1) b)
  simp_rw [hproduct] at h
  exact h

/-- Let k be a commutative ring and A a k-algebra ring. Write π_n : A ⊗[k] TensorPower k n A →
Cλ_n for the Connes projection and Ω_n(a) for cyclicFullTensor k A n a. For n : ℕ and a : Fin
(n + 1) → A, TensorPower.consCyclicOperator k A n (Ω_n(a)) = Ω_n(a). The cyclic operator
includes its degree sign. -/
theorem cyclicFullTensor_cyclic (n : ℕ) (a : Fin (n + 1) → A) :
    TensorPower.consCyclicOperator k A n (cyclicFullTensor k A n a) = cyclicFullTensor k A n a := by
  apply (TensorPower.consEquiv k A n).injective
  rw [TensorPower.consCyclicOperator_coordinates]
  simp only [cyclicFullTensor, LinearEquiv.apply_symm_apply]
  rw [MultilinearMap.alternatization_apply, map_sum]
  let ρ := finRotate (n + 1)
  let e : Equiv.Perm (Fin (n + 1)) ≃ Equiv.Perm (Fin (n + 1)) := Equiv.mulRight ρ.symm
  refine Fintype.sum_equiv e _ _ ?_
  intro σ
  change TensorPower.cyclicOperator k A n
      (σ.sign • PiTensorProduct.tprod k (a ∘ σ)) =
    (σ * ρ.symm).sign • PiTensorProduct.tprod k (a ∘ (σ * ρ.symm))
  rw [map_zsmul_unit, TensorPower.cyclicOperator_tprod]
  have hsign : (σ * ρ.symm).sign = σ.sign * (-1 : ℤˣ) ^ n := by
    rw [map_mul, Equiv.Perm.sign_symm, sign_finRotate, Nat.add_sub_cancel]
  have hs (x : TensorPower k (n + 1) A) : (-1 : ℤˣ) ^ n • x = (-1 : k) ^ n • x := by
    change (-1 : ℤ) ^ n • x = _
    simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using
      (Int.cast_smul_eq_zsmul k ((-1 : ℤ) ^ n) x).symm
  rw [hsign, mul_smul, hs]
  rfl

/-- Let k be a commutative ring and A a k-algebra ring. Write π_n : A ⊗[k] TensorPower k n A →
Cλ_n for the Connes projection and Ω_n(a) for cyclicFullTensor k A n a. For n : ℕ, j : ℤ and a
: Fin (n + 1) → A, cyclicPowerMap k A n j sends Ω_n(a) to itself. -/
theorem cyclicFullTensor_cyclicPower (n : ℕ) (j : ℤ) (a : Fin (n + 1) → A) :
    (ModuleCat.Algebra.Hochschild.NonUnital.cyclicPowerMap k A n j).hom
      (cyclicFullTensor k A n a) = cyclicFullTensor k A n a := by
  change TensorPower.consCyclicRepresentation k A n
    (Multiplicative.ofAdd (j : ZMod (n + 1))) (cyclicFullTensor k A n a) = _
  let t : ℕ := (j : ZMod (n + 1)).val
  have ht : (t : ZMod (n + 1)) = j := ZMod.natCast_zmod_val _
  rw [← ht, TensorPower.consCyclicRepresentation_natCast]
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply,
        ih, cyclicFullTensor_cyclic]

/-- Let k be a commutative ring and A a k-algebra ring, and let π_n be its Connes projection from
A ⊗[k] TensorPower k n A. For n : ℕ and j : ℤ, cyclicPowerMap k A n j ≫ π_n = π_n. Thus the
quotient map identifies each signed cyclic rotation with the unrotated tensor class. -/
theorem connesProjection_cyclicPower (n : ℕ) (j : ℤ) :
    ModuleCat.Algebra.Hochschild.NonUnital.cyclicPowerMap k A n j ≫
      ModuleCat.Algebra.Hochschild.Matrix.connesProjection k A n =
      ModuleCat.Algebra.Hochschild.Matrix.connesProjection k A n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
    (TensorPower.consCyclicRepresentation k A n
      (Multiplicative.ofAdd (j : ZMod (n + 1))) x) = _
  let t : ℕ := (j : ZMod (n + 1)).val
  have ht : (t : ZMod (n + 1)) = j := ZMod.natCast_zmod_val _
  rw [← ht, TensorPower.consCyclicRepresentation_natCast]
  exact ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative_cyclic_pow k A n t x

/-- Let k be a commutative ring and A a k-algebra ring. Write π_n : A ⊗[k] TensorPower k n A →
Cλ_n for the Connes projection and Ω_n(a) for cyclicFullTensor k A n a. For n : ℕ, i : Fin (n
+ 2) and a : Fin (n + 2) → A, (−1 : ℤ)^i.val • π_n(regularFace_i(Ω_(n+1)(a))) =
π_n(regularFace_0(Ω_(n+1)(a))). -/
theorem cyclicFullTensor_face (n : ℕ) (i : Fin (n + 2)) (a : Fin (n + 2) → A) :
    (-1 : ℤ) ^ i.val • ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
      ((ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n i).hom
        (cyclicFullTensor k A (n + 1) a)) =
      ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
        ((ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n 0).hom
          (cyclicFullTensor k A (n + 1) a)) := by
  have h := congrArg (fun f => f.hom (cyclicFullTensor k A (n + 1) a))
    (ModuleCat.Algebra.Hochschild.NonUnital.regularFace_weighted_conjugate k A n i)
  simp only [ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply] at h
  rw [cyclicFullTensor_cyclicPower] at h
  have hp := congrArg (fun f => f.hom
      ((ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n 0).hom
        (cyclicFullTensor k A (n + 1) a)))
    (connesProjection_cyclicPower k A n (i.val : ℤ))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hp
  calc
    _ = ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
        ((-1 : ℤ) ^ i.val •
          (ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n i).hom
            (cyclicFullTensor k A (n + 1) a)) := (map_zsmul _ _ _).symm
    _ = _ := (congrArg
      (ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n) h).trans hp

/-- Let k be a commutative ring and A a k-algebra ring. Write π_n : A ⊗[k] TensorPower k n A →
Cλ_n for the Connes projection and Ω_n(a) for cyclicFullTensor k A n a. For n : ℕ and a : Fin
(n + 2) → A, d_Cλ(n+1,n)(cyclicFullExterior k A (n + 1)(ιMulti a)) = (n + 2) •
π_n(regularFace_0(Ω_(n+1)(a))). The factor n + 2 is natural-number repeated addition, coming
from all signed regular faces. -/
theorem cyclicFullTensor_boundary_first (n : ℕ) (a : Fin (n + 2) → A) :
    ((Cλ k A).d (n + 1) n).hom
        (cyclicFullExterior k A (n + 1) (exteriorPower.ιMulti k (n + 2) a)) =
      (n + 2) • ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
        ((ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n 0).hom
          (cyclicFullTensor k A (n + 1) a)) := by
  rw [← cyclicFullTensor_projection]
  have hp := congrArg (fun f => f.hom (cyclicFullTensor k A (n + 1) a))
    (ModuleCat.Algebra.Hochschild.Matrix.connesProjection_boundary k A n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hp
  change ((Cλ k A).d (n + 1) n).hom
      (ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A (n + 1)
        (cyclicFullTensor k A (n + 1) a)) =
    ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
      (((ModuleCat.Algebra.Hochschild.NonUnital.bComplex k A).d (n + 1) n).hom
        (cyclicFullTensor k A (n + 1) a)) at hp
  have hb := congrArg (fun f => f.hom (cyclicFullTensor k A (n + 1) a))
    (ModuleCat.Algebra.Hochschild.NonUnital.bComplex_d k A n)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply] at hb
  refine hp.trans ?_
  calc
    _ = ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          (ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n i).hom
            (cyclicFullTensor k A (n + 1) a)) := congrArg _ hb
    _ = ∑ i : Fin (n + 2),
        ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
          ((-1 : ℤ) ^ i.val •
            (ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n i).hom
              (cyclicFullTensor k A (n + 1) a)) := map_sum _ _ _
    _ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
          ((ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n i).hom
            (cyclicFullTensor k A (n + 1) a)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact map_zsmul _ _ _
    _ = ∑ _i : Fin (n + 2),
        ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
          ((ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n 0).hom
            (cyclicFullTensor k A (n + 1) a)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact cyclicFullTensor_face k A n i a
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end ChevalleyEilenberg

end
