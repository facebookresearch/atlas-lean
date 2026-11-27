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
# Full alternation and fixed-first cyclic exterior maps

For a k-algebra ring A over a commutative ring k, the whole-tensor projection q_n to the
Connes quotient gives a multilinear map on n + 1 inputs. Full alternation induces an integral
linear map ⋀[k]^(n+1) A → Cλ_n with value ∑ σ, sign(σ) q_n(a ∘ σ).

The signed cyclic relation identifies this full sum with (n + 1) times the tail sum which
fixes a₀ and alternates the remaining n inputs. When k is a ℚ-algebra, multiplying the full
map by 1/(n + 1) yields exactly that tail formula. A second degree map multiplies this
normalization by (−1)^n. All these degree maps are natural for nonunital k-algebra
homomorphisms; the integral formulas do not use rational division.

See Weibel, *An Introduction to Homological Algebra*, Chapter 9, for cyclic homology and
exterior comparisons.
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

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For n : ℕ, cyclicMultilinear maps a : Fin (n + 1) → A to
q_n(PiTensorProduct.tprod k a). It is k-multilinear in all n + 1 inputs. -/
def cyclicMultilinear (n : ℕ) :
    MultilinearMap (RingHom.id k) (fun _ : Fin (n + 1) => A) ((Cλ k A).X n) :=
  (q k A n).compMultilinearMap (PiTensorProduct.tprod k)

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For n : ℕ, cyclicFullAlternating is the alternatization of
cyclicMultilinear. On a tuple a it is ∑ σ : Perm(Fin(n+1)), sign(σ) • q_n(tprod(a ∘ σ)), an
alternating map in all n + 1 inputs. -/
def cyclicFullAlternating (n : ℕ) : A [⋀^Fin (n + 1)]→ₗ[k] ((Cλ k A).X n) :=
  (cyclicMultilinear k A n).alternatization

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For n : ℕ, cyclicFullExterior : ⋀[k]^(n+1) A →ₗ[k] Cλ_n is the
linear map corresponding to the full alternating multilinear tensor projection. Its definition
uses the integral signed permutation sum. -/
def cyclicFullExterior (n : ℕ) : (⋀[k]^(n + 1) A) →ₗ[k] ((Cλ k A).X n) :=
  exteriorPower.alternatingMapLinearEquiv (cyclicFullAlternating k A n)

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For n : ℕ and a : Fin (n + 1) → A, cyclicFullExterior(ιMulti a) = ∑
σ : Perm(Fin(n+1)), sign(σ) • q_n(tprod(a ∘ σ)). The tuple is reindexed by σ itself, with the
permutation sign acting through the additive group. -/
theorem cyclicFullExterior_pure (n : ℕ) (a : Fin (n + 1) → A) :
    cyclicFullExterior k A n (exteriorPower.ιMulti k (n + 1) a) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), σ.sign • q k A n
        (PiTensorProduct.tprod k (a ∘ σ)) := by
  rw [cyclicFullExterior, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    cyclicFullAlternating, MultilinearMap.alternatization_apply]
  rfl

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For a : Fin (n + 1) → A, cyclicTailSum n a is ∑ σ : Perm(Fin n),
sign(σ) • [a₀ ⊗ tprod(j ↦ a_((σ j).succ))] in Cλ_n. Only the last n inputs are permuted in
this formula. -/
def cyclicTailSum (n : ℕ) (a : Fin (n + 1) → A) : (Cλ k A).X n :=
  ∑ σ : Equiv.Perm (Fin n), σ.sign •
    ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A n
      (a 0 ⊗ₜ[k] PiTensorProduct.tprod k (fun j => a (σ j).succ))

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For n : ℕ, j : Fin (n + 1) and a : Fin (n + 1) → A, let s_j =
Perm.shiftFirst n j. Then (−1 : ℤˣ)^(n*j.val) • q_n(tprod(a ∘ s_j.symm)) = q_n(tprod a). This
is the quotient's signed cyclic-rotation relation. -/
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

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For n : ℕ and a : Fin (n + 1) → A, cyclicFullExterior(ιMulti a) =
(n + 1) • cyclicTailSum n a, where the scalar on the right is natural-number repeated
addition. The equality is valid without division in k. -/
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

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. For a : Fin 1 → A, cyclicFullExterior in degree 0 sends ιMulti a to
cyclicTailSum 0 a. Both are the Connes class of the single input a₀. -/
theorem cyclicFullExterior_zero_pure (a : Fin 1 → A) :
    cyclicFullExterior k A 0 (exteriorPower.ιMulti k 1 a) = cyclicTailSum k A 0 a := by
  exact (cyclicFullExterior_eq_factor_tail k A 0 a).trans (one_nsmul _)

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. Let B be another k-algebra ring in the same carrier universe as A
and f : A →ₙₐ[k] B a nonunital k-algebra homomorphism. For n : ℕ, Cλ(f)_n ∘
cyclicFullExterior_A(n) = cyclicFullExterior_B(n) ∘ ⋀^(n+1) f, where Cλ(f) is the induced
Connes chain map. -/
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

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. Assume k is a ℚ-algebra. For n : ℕ, cyclicExterior is algebraMap ℚ
k ((n + 1 : ℚ)⁻¹) times cyclicFullExterior : ⋀[k]^(n+1) A →ₗ[k] Cλ_n. -/
def cyclicExterior (n : ℕ) : (⋀[k]^(n + 1) A) →ₗ[k] ((Cλ k A).X n) :=
  algebraMap ℚ k ((n + 1 : ℚ)⁻¹) • cyclicFullExterior k A n

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. Assume k is a ℚ-algebra. For every n : ℕ, cyclicExterior n =
algebraMap ℚ k ((n + 1 : ℚ)⁻¹) • cyclicFullExterior n. The factor is the number of inputs,
rather than a factorial. -/
theorem cyclicExterior_full (n : ℕ) :
    cyclicExterior k A n = algebraMap ℚ k ((n + 1 : ℚ)⁻¹) • cyclicFullExterior k A n := rfl

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. Assume k is a ℚ-algebra. For n : ℕ and a : Fin (n + 1) → A,
cyclicExterior n (ιMulti a) = cyclicTailSum n a, the signed permutation sum over the n tail
positions with a₀ fixed. -/
theorem cyclicExterior_pure (n : ℕ) (a : Fin (n + 1) → A) :
    cyclicExterior k A n (exteriorPower.ιMulti k (n + 1) a) = cyclicTailSum k A n a := by
  rw [cyclicExterior, LinearMap.smul_apply, cyclicFullExterior_eq_factor_tail]
  have hq : (n + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [← Nat.cast_smul_eq_nsmul k (n + 1), smul_smul,
    ← map_natCast (algebraMap ℚ k) (n + 1), ← map_mul, Nat.cast_add, Nat.cast_one,
    inv_mul_cancel₀ hq, map_one, one_smul]

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. Assume k is a ℚ-algebra. Let B be another k-algebra ring in the
same carrier universe as A and f : A →ₙₐ[k] B a nonunital k-algebra homomorphism. For n : ℕ,
Cλ(f)_n ∘ cyclicExterior_A(n) = cyclicExterior_B(n) ∘ ⋀^(n+1) f. -/
theorem cyclicExterior_natural {B : Type v} [Ring B] [Algebra k B]
    (f : A →ₙₐ[k] B) (n : ℕ) :
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f).f n).hom).comp
        (cyclicExterior k A n) =
      (cyclicExterior k B n).comp (exteriorPower.map (n + 1) (f : A →ₗ[k] B)) := by
  rw [cyclicExterior, cyclicExterior, LinearMap.comp_smul, LinearMap.smul_comp,
    cyclicFullExterior_natural]

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. Assume k is a ℚ-algebra. For n : ℕ, cyclicExteriorWeibel n :
⋀[k]^(n+1) A →ₗ[k] Cλ_n is (−1 : k)^n times cyclicExterior n. -/
def cyclicExteriorWeibel (n : ℕ) : (⋀[k]^(n + 1) A) →ₗ[k] ((Cλ k A).X n) :=
  (-1 : k) ^ n • cyclicExterior k A n

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. Assume k is a ℚ-algebra. For n : ℕ and a : Fin (n + 1) → A,
cyclicExteriorWeibel n (ιMulti a) = (−1 : k)^n • cyclicTailSum n a. -/
theorem cyclicExteriorWeibel_pure (n : ℕ) (a : Fin (n + 1) → A) :
    cyclicExteriorWeibel k A n (exteriorPower.ιMulti k (n + 1) a) =
      (-1 : k) ^ n • cyclicTailSum k A n a := by
  rw [cyclicExteriorWeibel, LinearMap.smul_apply, cyclicExterior_pure]

/-- Let k be a commutative ring and A a possibly noncommutative ring with a k-algebra structure.
Let Cλ_n be degree n of its Connes cyclic quotient and q_n : A^⊗(n+1) →ₗ[k] Cλ_n the
whole-tensor quotient map. Assume k is a ℚ-algebra. Let B be another k-algebra ring in the
same carrier universe as A and f : A →ₙₐ[k] B a nonunital k-algebra homomorphism. For n : ℕ,
Cλ(f)_n ∘ cyclicExteriorWeibel_A(n) = cyclicExteriorWeibel_B(n) ∘ ⋀^(n+1) f. -/
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
