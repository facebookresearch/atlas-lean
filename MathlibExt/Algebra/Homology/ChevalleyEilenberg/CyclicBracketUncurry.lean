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
# The bracket sum in the cyclic exterior comparison

Associative multiplication followed by the fixed-first-factor alternating
map gives the bilinear input. Double uncurrying pairs opposite products into
Lie brackets, preserving the order of the twice-removed tuple. This yields
the integral bracket-tail formula for the full exterior boundary.
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

/-- The original product of the two singled-out inputs, with the same alternating tail. -/
def cyclicTailAlternating (n : ℕ) : A →ₗ[k] A [⋀^Fin n]→ₗ[k] ((Cλ k A).X n) :=
  MultilinearMap.alternatizeTail (cyclicMultilinear k A n).curryLeft

/-- The native alternating tail has exactly the original fixed-first-factor formula. -/
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

/-- Original multiplication into the integral fixed-first alternating tail. -/
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

/-- The twice uncurried original product of two inputs into the integral tail sum. -/
def cyclicTailProductUncurry (n : ℕ) : A [⋀^Fin (n + 2)]→ₗ[k] ((Cλ k A).X n) :=
  AlternatingMap.alternatizeUncurryFin
    (AlternatingMap.alternatizeUncurryFinLM.comp (cyclicTailProductCurry k A n))

/-- The native double-uncurrying formula supplies the bracket-tail sum integrally. -/
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

/-- The integral full exterior boundary has the exact remaining-input factor times the tail
bracket sum. -/
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
