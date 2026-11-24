/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Data.Fin.Tuple.StableSort
public import MathlibExt.Combinatorics.Perm.EulerianLabelings
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Tactic.Ring

/-!
# Integral signed convolution operations

Each finite alphabet labeling contributes its stable-sorting permutation
with its integer sign. A product-alphabet bijection proves multiplication
of convolution parameters over every commutative coefficient ring.

The signed positive-integer operation multiplies the convolution value at
`m` by `(-1)^(m - 1)`. Its composition consequently has the parity scalar
`(-1)^((l - 1)(m - 1))`. The convolution itself is defined for all natural
parameters, including zero.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

universe u

namespace Equiv.Perm

variable (R : Type u) [CommRing R]

/-- The actual signed permutation sum of all original finite alphabet labelings. -/
def integralConvolutionElement (n m : ℕ) : MonoidAlgebra R (Perm (Fin n)) :=
  ∑ f : Fin n → Fin m, MonoidAlgebra.single (Tuple.sort f) (((Tuple.sort f).sign : ℤ) : R)

/-- The actual integral coefficient is the cardinality of its sorting fibre times its sign. -/
theorem integralConvolutionElement_eq_fiber_sum (n m : ℕ) :
    integralConvolutionElement R n m =
      ∑ σ : Perm (Fin n), MonoidAlgebra.single σ
        ((Fintype.card {f : Fin n → Fin m // Tuple.sort f = σ} : R) * (((σ.sign : ℤ) : R))) := by
  classical
  let e := Equiv.sigmaFiberEquiv (fun f : Fin n → Fin m => Tuple.sort f)
  rw [integralConvolutionElement,
    ← e.sum_comp (fun f => MonoidAlgebra.single (Tuple.sort f) (((Tuple.sort f).sign : ℤ) : R)),
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro σ _
  have hconst (f : {f : Fin n → Fin m // Tuple.sort f = σ}) :
      MonoidAlgebra.single (Tuple.sort (e ⟨σ, f⟩)) (((Tuple.sort (e ⟨σ, f⟩)).sign : ℤ) : R) =
        MonoidAlgebra.single σ (((σ.sign : ℤ) : R)) := by
    change MonoidAlgebra.single (Tuple.sort f.val) (((Tuple.sort f.val).sign : ℤ) : R) = _
    rw [f.property]
  simp_rw [hconst]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul R,
    MonoidAlgebra.smul_single, smul_eq_mul]

/-- The original coefficient is computed by the actual sorting fibre, over every coefficient ring. -/
theorem integralConvolutionElement_coefficient (n m : ℕ) (σ : Perm (Fin n)) :
    (integralConvolutionElement R n m).coeff σ =
      (Fintype.card {f : Fin n → Fin m // Tuple.sort f = σ} : R) * (((σ.sign : ℤ) : R)) := by
  classical
  rw [integralConvolutionElement_eq_fiber_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The actual positive-degree integral coefficient is the native descent-binomial count. -/
theorem integralConvolutionElement_coefficient_succ (n m : ℕ) (σ : Perm (Fin (n + 1))) :
    (integralConvolutionElement R (n + 1) m).coeff σ =
      (((n + m - descentNumber σ).choose (n + 1) : ℕ) : R) * (((σ.sign : ℤ) : R)) := by
  rw [integralConvolutionElement_coefficient, card_sortFiber]

variable {S : Type*} [CommRing S]

/-- A coefficient ring map preserves the original integral operation. -/
theorem map_integralConvolutionElement (f : R →+* S) (n m : ℕ) :
    (MonoidAlgebra.mapRingHom (Perm (Fin n)) f) (integralConvolutionElement R n m) =
      integralConvolutionElement S n m := by
  classical
  rw [integralConvolutionElement, map_sum, integralConvolutionElement]
  simp only [MonoidAlgebra.mapRingHom_single, map_intCast]

/-- The native product-alphabet sorting bijection gives convolution composition. -/
theorem integralConvolutionElement_mul (n a b : ℕ) :
    integralConvolutionElement R n a * integralConvolutionElement R n b =
      integralConvolutionElement R n (a * b) := by
  classical
  let e := Tuple.successiveStableFinLabelsEquiv n a b
  conv_rhs => rw [Nat.mul_comm a b]
  unfold integralConvolutionElement
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, MonoidAlgebra.single_mul_single]
  have hsign (f : Fin n → Fin a) (g : Fin n → Fin b) :
      (((Tuple.sort f).sign : ℤ) : R) * (((Tuple.sort g).sign : ℤ) : R) =
        (((Tuple.sort f * Tuple.sort g).sign : ℤ) : R) := by
    rw [Equiv.Perm.sign_mul]
    simp only [Units.val_mul, Int.cast_mul]
  simp_rw [hsign]
  rw [← Fintype.sum_prod_type' (fun (f : Fin n → Fin a) (g : Fin n → Fin b) =>
    MonoidAlgebra.single (Tuple.sort f * Tuple.sort g)
      (((Tuple.sort f * Tuple.sort g).sign : ℤ) : R))]
  rw [← e.symm.sum_comp (fun z => MonoidAlgebra.single (Tuple.sort z.1 * Tuple.sort z.2)
    (((Tuple.sort z.1 * Tuple.sort z.2).sign : ℤ) : R))]
  apply Finset.sum_congr rfl
  intro h _
  have hp := Tuple.sort_successiveStableFinLabelsEquiv n a b (e.symm h)
  rw [show Tuple.successiveStableFinLabelsEquiv n a b (e.symm h) = h from e.apply_symm_apply h] at hp
  rw [← hp]

/-- The original degree-zero empty word has the actual unit convolution for every alphabet. -/
theorem integralConvolutionElement_degree_zero (m : ℕ) :
    integralConvolutionElement R 0 m = 1 := by
  classical
  letI : Unique (Fin 0 → Fin m) :=
    { default := Fin.elim0, uniq := fun f => funext (fun i => Fin.elim0 i) }
  have hs : Tuple.sort (default : Fin 0 → Fin m) = 1 := Subsingleton.elim _ _
  rw [integralConvolutionElement, Fintype.sum_unique, hs]
  simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, ← MonoidAlgebra.one_def]

/-- The empty alphabet has no positive-degree labels, so the actual operation is zero. -/
theorem integralConvolutionElement_zero_parameter (n : ℕ) (hn : 0 < n) :
    integralConvolutionElement R n 0 = 0 := by
  classical
  haveI : IsEmpty (Fin n → Fin 0) :=
    ⟨fun f => Fin.elim0 (f ⟨0, hn⟩)⟩
  rw [integralConvolutionElement, Finset.univ_eq_empty, Finset.sum_empty]

/-- The signed integer operation includes `(-1)^(m - 1)` at positive parameter `m`.
The convolution operation is defined for every natural parameter. -/
def trueLambdaElement (n m : ℕ) (_hm : 0 < m) : MonoidAlgebra R (Perm (Fin n)) :=
  (-1 : R) ^ (m - 1) • integralConvolutionElement R n m

/-- In chain degree zero, every positive true-lambda parameter retains its exact sign. -/
theorem trueLambdaElement_degree_zero (m : ℕ) (hm : 0 < m) :
    trueLambdaElement R 0 m hm = (-1 : R) ^ (m - 1) • (1 : MonoidAlgebra R (Perm (Fin 0))) := by
  rw [trueLambdaElement, integralConvolutionElement_degree_zero]

private theorem trueLambda_sign_composition (a b : ℕ) :
    (-1 : R) ^ a * (-1 : R) ^ b =
      (-1 : R) ^ (a * b) * (-1 : R) ^ ((a + 1) * (b + 1) - 1) := by
  have he : (a + 1) * (b + 1) - 1 = a * b + a + b := by
    calc
      _ = (a * b + a + b + 1) - 1 := by congr 1; ring
      _ = a * b + a + b := Nat.add_sub_cancel _ _
  have ht : a * b + (a * b + a + b) = 2 * (a * b) + (a + b) := by ring
  rw [he]
  conv_lhs => rw [← pow_add]
  conv_rhs => rw [← pow_add, ht, pow_add, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]

/-- True positive-integer lambda operations compose with the actual parity scalar.
The scalar is derived from their original definition, not from a renamed convolution law. -/
theorem trueLambdaElement_mul (n l m : ℕ) (hl : 0 < l) (hm : 0 < m) :
    trueLambdaElement R n l hl * trueLambdaElement R n m hm =
      (-1 : R) ^ ((l - 1) * (m - 1)) • trueLambdaElement R n (l * m) (Nat.mul_pos hl hm) := by
  cases l with
  | zero => omega
  | succ a =>
    cases m with
    | zero => omega
    | succ b =>
      rw [trueLambdaElement, trueLambdaElement, smul_mul_assoc, mul_smul_comm,
        integralConvolutionElement_mul, smul_smul, trueLambdaElement, smul_smul]
      simp only [Nat.succ_sub_one]
      rw [trueLambda_sign_composition]

end Equiv.Perm
