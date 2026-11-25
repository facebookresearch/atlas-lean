/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.ConnesTrace
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Canonical
public import MathlibExt.Algebra.Homology.ChainComplex.PositiveTail
public import MathlibExt.Algebra.Homology.HomologicalComplexRescaling
public import Mathlib.GroupTheory.Perm.Fin
public import MathlibExt.GroupTheory.Perm.CyclicFirstCoordinate
public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Alternating exterior-to-Connes maps

Full alternatization constructs an integral permutation sum from exterior
powers to the Connes quotient. Over a commutative ground ring `k` with
`Algebra ℚ k`, division by the number of input factors identifies this sum
with the ordered tail antisymmetrization.

The signed cyclic relation is imposed by the Connes projection. The
`cyclicExteriorWeibel` variant multiplies the rational map by `(-1)^n` in
degree `n`; the integral and rational maps remain distinct constructions.
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
local notation "q" => ModuleCat.Algebra.Hochschild.Matrix.connesTensorRepresentative

/-- The original whole tensor generator followed by the Connes projection. -/
def cyclicMultilinear (n : ℕ) : MultilinearMap k (fun _ : Fin (n + 1) => A) ((Cλ k A).X n) :=
  (q k A n).compMultilinearMap (PiTensorProduct.tprod k)

/-- Integral full native alternatization, with no normalization or division. -/
def cyclicFullAlternating (n : ℕ) : A [⋀^Fin (n + 1)]→ₗ[k] ((Cλ k A).X n) :=
  (cyclicMultilinear k A n).alternatization

/-- The integral full-permutation map on the existing exterior-power object. -/
def cyclicFullExterior (n : ℕ) : (⋀[k]^(n + 1) A) →ₗ[k] ((Cλ k A).X n) :=
  exteriorPower.alternatingMapLinearEquiv (cyclicFullAlternating k A n)

/-- Exact integral full-permutation formula, with the original ordered tensor representatives. -/
theorem cyclicFullExterior_pure (n : ℕ) (a : Fin (n + 1) → A) :
    cyclicFullExterior k A n (exteriorPower.ιMulti k (n + 1) a) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), σ.sign • q k A n
        (PiTensorProduct.tprod k (a ∘ σ)) := by
  rw [cyclicFullExterior, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    cyclicFullAlternating, MultilinearMap.alternatization_apply]
  rfl

/-- The ordered tail sum, before establishing its exterior descent. -/
def cyclicTailSum (n : ℕ) (a : Fin (n + 1) → A) : (Cλ k A).X n :=
  ∑ σ : Equiv.Perm (Fin n), σ.sign •
    ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
      (a 0 ⊗ₜ[k] PiTensorProduct.tprod k (fun j => a (σ j).succ))

/-- The signed native rotation reindexes a representative without changing its quotient class. -/
private theorem cyclic_shift_representative (n : ℕ) (j : Fin (n + 1))
    (a : Fin (n + 1) → A) :
    (-1 : ℤˣ) ^ (n * j.val) •
      q k A n (PiTensorProduct.tprod k (a ∘ (Equiv.Perm.shiftFirst n j).symm)) =
      q k A n (PiTensorProduct.tprod k a) := by
  have h := ModuleCat.Algebra.Hochschild.Matrix.connesTensorRepresentative_cyclic_pow
    k A n j.val (PiTensorProduct.tprod k a)
  rw [TensorPower.cyclicOperator_pow_tprod, map_smul] at h
  have hs (x : (Cλ k A).X n) :
      (-1 : ℤˣ) ^ (n * j.val) • x = (-1 : k) ^ (n * j.val) • x := by
    change ((-1 : ℤ) ^ (n * j.val)) • x = _
    have hi := Int.cast_smul_eq_zsmul k ((-1 : ℤ) ^ (n * j.val)) x
    simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using hi.symm
  simpa only [Equiv.Perm.shiftFirst, Function.comp_def, hs] using h

/-- The integral full sum is exactly the number of input factors times the tail sum. -/
theorem cyclicFullExterior_eq_factor_tail (n : ℕ) (a : Fin (n + 1) → A) :
    cyclicFullExterior k A n (exteriorPower.ιMulti k (n + 1) a) =
      (n + 1) • cyclicTailSum k A n a := by
  rw [cyclicFullExterior_pure]
  have hsum :
      (∑ τ : Equiv.Perm (Fin (n + 1)), τ.sign • q k A n
        (PiTensorProduct.tprod k (a ∘ τ))) =
      ∑ p : Fin (n + 1) × Equiv.Perm (Fin n), p.2.sign •
        ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
          (a 0 ⊗ₜ[k] PiTensorProduct.tprod k (fun l => a (p.2 l).succ)) := by
    apply Fintype.sum_equiv (Equiv.Perm.cyclicFirstEquiv n).symm
    intro τ
    obtain ⟨⟨j, σ⟩, rfl⟩ := (Equiv.Perm.cyclicFirstEquiv n).surjective τ
    rw [(Equiv.Perm.cyclicFirstEquiv n).symm_apply_apply]
    rw [Equiv.Perm.cyclicFirstEquiv_sign, mul_smul]
    have ht : a ∘ Equiv.Perm.cyclicFirstEquiv n (j, σ) =
        (a ∘ Equiv.Perm.fixFirst n σ) ∘ (Equiv.Perm.shiftFirst n j).symm := rfl
    rw [ht, cyclic_shift_representative]
    change σ.sign • ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
        ((TensorPower.consEquiv k A n).symm
          (PiTensorProduct.tprod k (a ∘ Equiv.Perm.fixFirst n σ))) = _
    have hcons := TensorPower.consEquiv_symm_tprod k A n (a ∘ Equiv.Perm.fixFirst n σ)
    have htail : Fin.tail (a ∘ Equiv.Perm.fixFirst n σ) = fun l => a (σ l).succ := by
      funext l
      simp only [Fin.tail, Function.comp_apply, Equiv.Perm.fixFirst_succ]
    rw [hcons, Function.comp_apply, Equiv.Perm.fixFirst_zero, htail]
  rw [hsum, Fintype.sum_prod_type]
  change (∑ _ : Fin (n + 1), cyclicTailSum k A n a) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- The degree-zero full and tail sums are the same one-factor representative. -/
theorem cyclicFullExterior_zero_pure (a : Fin 1 → A) :
    cyclicFullExterior k A 0 (exteriorPower.ιMulti k 1 a) = cyclicTailSum k A 0 a := by
  exact (cyclicFullExterior_eq_factor_tail k A 0 a).trans (one_nsmul _)

/-- Every coefficient map commutes with the original full alternating representative. -/
theorem cyclicFullExterior_natural {B : Type v} [Ring B] [Algebra k B]
    (f : A →ₙₐ[k] B) (n : ℕ) :
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f).f n).hom).comp
        (cyclicFullExterior k A n) =
      (cyclicFullExterior k B n).comp (exteriorPower.map (n + 1) (f : A →ₗ[k] B)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f).f n).hom
      (cyclicFullExterior k A n (exteriorPower.ιMulti k (n + 1) a)) =
    cyclicFullExterior k B n
      (exteriorPower.map (n + 1) (f : A →ₗ[k] B) (exteriorPower.ιMulti k (n + 1) a))
  rw [exteriorPower.map_apply_ιMulti, cyclicFullExterior_pure, cyclicFullExterior_pure, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  let F := (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f).f n
  have hm : F.hom (σ.sign • q k A n (PiTensorProduct.tprod k (a ∘ σ))) =
      σ.sign • F.hom (q k A n (PiTensorProduct.tprod k (a ∘ σ))) :=
    map_zsmul_unit F.hom σ.sign _
  exact hm.trans (by
    simpa only [PiTensorProduct.map_tprod, Function.comp_def] using
      congrArg (fun z => σ.sign • z)
        (ModuleCat.Algebra.Hochschild.Matrix.connesTensorRepresentative_natural k A f n
          (PiTensorProduct.tprod k (a ∘ σ))))

section Rational

variable [Algebra ℚ k]

/-- The exterior-to-Connes degree map, obtained from the native full alternatization. -/
def cyclicExterior (n : ℕ) : (⋀[k]^(n + 1) A) →ₗ[k] ((Cλ k A).X n) :=
  algebraMap ℚ k ((n + 1 : ℚ)⁻¹) • cyclicFullExterior k A n

/-- The rational normalization is only the number of input factors, never a factorial. -/
theorem cyclicExterior_full (n : ℕ) :
    cyclicExterior k A n = algebraMap ℚ k ((n + 1 : ℚ)⁻¹) • cyclicFullExterior k A n := rfl

/-- The normalized map is precisely the tail antisymmetrization, with no extra factor. -/
theorem cyclicExterior_pure (n : ℕ) (a : Fin (n + 1) → A) :
    cyclicExterior k A n (exteriorPower.ιMulti k (n + 1) a) = cyclicTailSum k A n a := by
  rw [cyclicExterior, LinearMap.smul_apply, cyclicFullExterior_eq_factor_tail]
  have hq : (n + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [← Nat.cast_smul_eq_nsmul k (n + 1), smul_smul,
    ← map_natCast (algebraMap ℚ k) (n + 1), ← map_mul, Nat.cast_add, Nat.cast_one,
    inv_mul_cancel₀ hq, map_one, one_smul]

/-- The normalized original exterior map has the same coefficient naturality. -/
theorem cyclicExterior_natural {B : Type v} [Ring B] [Algebra k B]
    (f : A →ₙₐ[k] B) (n : ℕ) :
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f).f n).hom).comp
        (cyclicExterior k A n) =
      (cyclicExterior k B n).comp (exteriorPower.map (n + 1) (f : A →ₗ[k] B)) := by
  rw [cyclicExterior, cyclicExterior, LinearMap.comp_smul, LinearMap.smul_comp,
    cyclicFullExterior_natural]

/-- The signed cyclic exterior map with degree factor `(-1)^n`. -/
def cyclicExteriorWeibel (n : ℕ) : (⋀[k]^(n + 1) A) →ₗ[k] ((Cλ k A).X n) :=
  (-1 : k) ^ n • cyclicExterior k A n

/-- The signed cyclic exterior map is the tail sum multiplied by `(-1)^n`. -/
theorem cyclicExteriorWeibel_pure (n : ℕ) (a : Fin (n + 1) → A) :
    cyclicExteriorWeibel k A n (exteriorPower.ιMulti k (n + 1) a) =
      (-1 : k) ^ n • cyclicTailSum k A n a := by
  rw [cyclicExteriorWeibel, LinearMap.smul_apply, cyclicExterior_pure]

/-- The degree sign preserves algebra naturality. -/
theorem cyclicExteriorWeibel_natural {B : Type v} [Ring B] [Algebra k B]
    (f : A →ₙₐ[k] B) (n : ℕ) :
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f).f n).hom).comp
        (cyclicExteriorWeibel k A n) =
      (cyclicExteriorWeibel k B n).comp (exteriorPower.map (n + 1) (f : A →ₗ[k] B)) := by
  rw [cyclicExteriorWeibel, cyclicExteriorWeibel, LinearMap.comp_smul, LinearMap.smul_comp,
    cyclicExterior_natural]

end Rational

end ChevalleyEilenberg

end
