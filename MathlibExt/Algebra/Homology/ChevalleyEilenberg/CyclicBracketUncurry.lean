/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CyclicAlternatization
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import MathlibExt.LinearAlgebra.Alternating.HeadAntisymmetrization

/-!
# Lie brackets from alternating uncurrying of cyclic tail products

Let A be a k-algebra ring over a commutative ring k. Fixing one input of the cyclic tensor
projection and alternating the last n inputs gives a map T_n(x; a). Applying it to the ordered
product x*y gives a bilinear family. Twice alternating the uncurry operation pairs x*y with
y*x, so their difference is the associative Lie bracket [x,y].

On n + 2 inputs a, the resulting alternating map is the sum over i : Fin(n+1) and j ≥ i of
(−1)^(i+j) times the tail sum with first input [a_i,a_(j+1)]. Its tail deletes position i
first and then position j in the shortened tuple. Applying the integral full exterior map to
the negative CE boundary equals (n + 1) times this bracket-tail map.
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

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For n : ℕ, cyclicTailAlternating n : A →ₗ[k] Alt(Fin n, A; Cλ_n)
fixes the first input x and alternates the remaining n. Its value on a tail a is cyclicTailSum
n (Fin.cons x a). -/
def cyclicTailAlternating (n : ℕ) : A →ₗ[k] A [⋀^Fin n]→ₗ[k] ((Cλ k A).X n) :=
  MultilinearMap.alternatizeTail (cyclicMultilinear k A n).curryLeft

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For x : A and a : Fin n → A, cyclicTailAlternating n x a =
cyclicTailSum n (Fin.cons x a), with signed permutations of the tail positions only. -/
theorem cyclicTailAlternating_apply (n : ℕ) (x : A) (a : Fin n → A) :
    cyclicTailAlternating k A n x a = cyclicTailSum k A n (Fin.cons x a) := by
  change ((cyclicMultilinear k A n).curryLeft x).alternatization a =
    cyclicTailSum k A n (Fin.cons x a)
  rw [MultilinearMap.alternatization_apply, cyclicTailSum]
  simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.curryLeft_apply,
    cyclicMultilinear, LinearMap.compMultilinearMap_apply,
    ModuleCat.Algebra.Hochschild.Matrix.connesTensorRepresentative,
    LinearMap.comp_apply, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro σ _
  change σ.sign • ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
      ((TensorPower.consEquiv k A n).symm
        (PiTensorProduct.tprod k (Fin.cons x (fun j => a (σ j))))) = _
  exact congrArg (fun y => σ.sign •
      ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n y)
    (TensorPower.consEquiv_symm_tprod k A n (Fin.cons x (fun j => a (σ j))))

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For n : ℕ, cyclicTailProductCurry is the k-bilinear map in x, y
with values in alternating n-tail maps, defined by (x,y;a) ↦ cyclicTailAlternating n (x*y) a. -/
def cyclicTailProductCurry (n : ℕ) :
    A →ₗ[k] A →ₗ[k] A [⋀^Fin n]→ₗ[k] ((Cλ k A).X n) where
  toFun x := (cyclicTailAlternating k A n).comp (LinearMap.mul k A x)
  map_add' x y := by
    ext z a
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mul_apply_apply,
      map_add, LinearMap.add_apply]
  map_smul' c x := by
    ext z a
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mul_apply_apply,
      map_smul, LinearMap.smul_apply]
    rfl

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For n : ℕ, applying the alternating uncurry operation twice to
cyclicTailProductCurry gives cyclicTailProductUncurry : Alt(Fin(n+2), A; Cλ_n). The two orders
of the singled-out multiplication contribute their commutator. -/
def cyclicTailProductUncurry (n : ℕ) : A [⋀^Fin (n + 2)]→ₗ[k] ((Cλ k A).X n) :=
  AlternatingMap.alternatizeUncurryFin
    (AlternatingMap.alternatizeUncurryFinLM.comp (cyclicTailProductCurry k A n))

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For a : Fin (n + 2) → A, cyclicTailProductUncurry n a = ∑ i :
Fin(n+1), ∑ j ≥ i, (−1 : ℤ)^(i.val+j.val) • cyclicTailSum n (Fin.cons
⁅a_(i.castSucc),a_(j.succ)⁆ (j.removeNth(i.castSucc.removeNth a))). The bracket is a_i*a_(j+1)
− a_(j+1)*a_i; the two removals occur in the displayed order. -/
theorem cyclicTailProductUncurry_pure (n : ℕ) (a : Fin (n + 2) → A) :
    cyclicTailProductUncurry k A n a =
      ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i,
        (-1 : ℤ) ^ (i.val + j.val) • cyclicTailSum k A n
          (Fin.cons ⁅a i.castSucc, a j.succ⁆ (j.removeNth (i.castSucc.removeNth a))) := by
  rw [cyclicTailProductUncurry,
    AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change cyclicTailAlternating k A n (a i.castSucc * a j.succ)
      (j.removeNth (i.castSucc.removeNth a)) -
    cyclicTailAlternating k A n (a j.succ * a i.castSucc)
      (j.removeNth (i.castSucc.removeNth a)) = _
  have h := congrArg (fun f : A [⋀^Fin n]→ₗ[k] ((Cλ k A).X n) =>
      f (j.removeNth (i.castSucc.removeNth a)))
    ((cyclicTailAlternating k A n).map_sub (a i.castSucc * a j.succ)
      (a j.succ * a i.castSucc))
  exact h.symm.trans (by
    rw [← LieRing.of_associative_ring_bracket, cyclicTailAlternating_apply])

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. Give A its associative commutator Lie bracket. For n : ℕ and a :
Fin (n + 2) → A, cyclicFullExterior n (−differential k A (n + 1)(ιMulti a)) = (n + 1) •
cyclicTailProductUncurry n a. The source boundary lowers exterior degree n + 2 to n + 1, and
the right side uses the signed bracket-tail sum. -/
theorem cyclicFullExterior_positive_boundary_factor (n : ℕ) (a : Fin (n + 2) → A) :
    cyclicFullExterior k A n
        (-differential k A (n + 1) (exteriorPower.ιMulti k (n + 2) a)) =
      (n + 1) • cyclicTailProductUncurry k A n a := by
  rw [map_neg, differential_apply_ιMulti]
  unfold bracketBoundary
  rw [map_sum, ← Finset.sum_neg_distrib, cyclicTailProductUncurry_pure]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, cyclicFullExterior_eq_factor_tail]
  have hs (x : (Cλ k A).X n) :
      (-1 : k) ^ (i.val + j.val + 1) • x = (-1 : ℤ) ^ (i.val + j.val + 1) • x := by
    simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using
      Int.cast_smul_eq_zsmul k ((-1 : ℤ) ^ (i.val + j.val + 1)) x
  rw [hs, pow_succ, mul_neg_one, neg_smul, neg_neg, smul_comm]
  rfl

end ChevalleyEilenberg

end
