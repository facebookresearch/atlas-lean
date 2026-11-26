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

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.MoritaFinite
public import Mathlib.Data.Fintype.BigOperators

/-!
# Unit frames for composite bimodule contractions

Let R and S be rings, P an R–S bimodule and Q an S–R bimodule in
independent carrier universes, with commuting actions. Let
u : P ⊗_S Q ≅ R and w : Q ⊗_R P ≅ S be bimodule equivalences,
and U the normalized R-valued contraction.

Choose finite pure expressions U⁻¹(1) = ∑_j [p_j ⊗ q_j] and
w⁻¹(1) = ∑_k [q_k ⊗ p_k]. On J × K define
a^R_(j,k) = U([p_k ⊗ q_j]), b^R_(j,k) = U([p_j ⊗ q_k]),
a^S_(j,k) = w([q_j ⊗ p_k]), b^S_(j,k) = w([q_k ⊗ p_j]).
The composite unit frames satisfy ∑ b^R_i a^R_i = 1_R and
∑ b^S_i a^S_i = 1_S. The product order is right coefficient times
left coefficient in each ring.
-/

@[expose] public section

noncomputable section

open MulOpposite
open scoped TensorProduct

universe r s p q

namespace TensorProduct.Balanced.Morita

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (P : Type p) (Q : Type q) [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  (u : letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := leftModule ℤ S R P Q
    letI := rightModule ℤ S R P Q
    ∀ (r : R) (b : TensorProduct.Balanced ℤ S P Q), u (r • b) = r * u b)
  (w : letI := leftModule ℤ R S Q P
    letI := rightModule ℤ R S Q P
    TensorProduct.Balanced ℤ R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hw : letI := leftModule ℤ R S Q P
    letI := rightModule ℤ R S Q P
    ∀ (s : S) (b : TensorProduct.Balanced ℤ R Q P), w (s • b) = s * w b)

local notation "U" => normalizedContraction R S P Q u w hw
local notation "J" => unitSupport R S P Q U
local notation "K" => unitSupport S R Q P w

include u w hw in
/-- Let R and S be rings, P an R–S bimodule and Q an S–R bimodule,
with commuting actions on additive commutative groups.
Let u : P ⊗_S Q ≅ R be right R-linear and w : Q ⊗_R P ≅ S
be right S-linear and left S-equivariant. Write U for the normalized
right R-linear contraction. Let J index a finite pure expression for
U⁻¹(1), with entries (p_j, q_j), and K for w⁻¹(1), with entries (q_k, p_k).
This is the finite product index J × K for the two composite coefficient
families. It uses the chosen inverse-unit supports, with no finite index
supplied separately. -/
abbrev compositeIndex := J × K

include u w hw in
/-- Let R and S be rings, P an R–S bimodule and Q an S–R bimodule,
with commuting actions on additive commutative groups.
Let u : P ⊗_S Q ≅ R be right R-linear and w : Q ⊗_R P ≅ S
be right S-linear and left S-equivariant. Write U for the normalized
right R-linear contraction. Let J index a finite pure expression for
U⁻¹(1), with entries (p_j, q_j), and K for w⁻¹(1), with entries (q_k, p_k).
The left coefficient of the R-valued composite at (j, k) is
a^R_(j,k) = U([p_k ⊗ q_j]). -/
def compositeRLeft (i : compositeIndex R S P Q u w hw) : R :=
  U (mk ℤ S P Q i.2.val.2 i.1.val.2)

include u w hw in
/-- Let R and S be rings, P an R–S bimodule and Q an S–R bimodule,
with commuting actions on additive commutative groups.
Let u : P ⊗_S Q ≅ R be right R-linear and w : Q ⊗_R P ≅ S
be right S-linear and left S-equivariant. Write U for the normalized
right R-linear contraction. Let J index a finite pure expression for
U⁻¹(1), with entries (p_j, q_j), and K for w⁻¹(1), with entries (q_k, p_k).
The right coefficient of the R-valued composite at (j, k) is
b^R_(j,k) = U([p_j ⊗ q_k]). -/
def compositeRRight (i : compositeIndex R S P Q u w hw) : R :=
  U (mk ℤ S P Q i.1.val.1 i.2.val.1)

include u w hw in
/-- Let R and S be rings, P an R–S bimodule and Q an S–R bimodule,
with commuting actions on additive commutative groups.
Let u : P ⊗_S Q ≅ R be right R-linear and w : Q ⊗_R P ≅ S
be right S-linear and left S-equivariant. Write U for the normalized
right R-linear contraction. Let J index a finite pure expression for
U⁻¹(1), with entries (p_j, q_j), and K for w⁻¹(1), with entries (q_k, p_k).
The left coefficient of the S-valued composite at (j, k) is
a^S_(j,k) = w([q_j ⊗ p_k]). -/
def compositeSLeft (i : compositeIndex R S P Q u w hw) : S :=
  w (mk ℤ R Q P i.1.val.2 i.2.val.2)

include u w hw in
/-- Let R and S be rings, P an R–S bimodule and Q an S–R bimodule,
with commuting actions on additive commutative groups.
Let u : P ⊗_S Q ≅ R be right R-linear and w : Q ⊗_R P ≅ S
be right S-linear and left S-equivariant. Write U for the normalized
right R-linear contraction. Let J index a finite pure expression for
U⁻¹(1), with entries (p_j, q_j), and K for w⁻¹(1), with entries (q_k, p_k).
The right coefficient of the S-valued composite at (j, k) is
b^S_(j,k) = w([q_k ⊗ p_j]). -/
def compositeSRight (i : compositeIndex R S P Q u w hw) : S :=
  w (mk ℤ R Q P i.2.val.1 i.1.val.1)

include u hu w hw in
/-- Let R and S be rings, P an R–S bimodule and Q an S–R bimodule,
with commuting actions on additive commutative groups.
Let u : P ⊗_S Q ≅ R and w : Q ⊗_R P ≅ S be bimodule equivalences.
Write U for the normalized R-valued contraction obtained from u and w.
For p, p′ ∈ P and q, q′ ∈ Q, the normalized contraction satisfies
U([p ⊗ q]) U([p′ ⊗ q′]) =
U([p ⊗ (w([q ⊗ p′]) • q′)]).
The S-valued contraction acts on q′ on the left inside the final tensor. -/
theorem normalizedR_pair_mul (p : P) (q : Q) (p' : P) (q' : Q) :
    U (mk ℤ S P Q p q) * U (mk ℤ S P Q p' q') =
      U (mk ℤ S P Q p (w (mk ℤ R Q P q p') • q')) := by
  let := rightModule ℤ S R P Q
  calc
    _ = U (op (U (mk ℤ S P Q p' q')) • mk ℤ S P Q p q) :=
      ((U).map_smul (op (U (mk ℤ S P Q p' q'))) (mk ℤ S P Q p q)).symm
    _ = U (mk ℤ S P Q p (op (U (mk ℤ S P Q p' q')) • q)) :=
      congrArg U (rightModule_smul_mk ℤ S R P Q _ p q)
    _ = _ := congrArg (fun y : Q => U (mk ℤ S P Q p y))
      (normalized_q R S P Q u hu w hw p' q q')

include u hu w hw in
/-- Let R and S be rings, P an R–S bimodule and Q an S–R bimodule,
with commuting actions on additive commutative groups.
Let u : P ⊗_S Q ≅ R and w : Q ⊗_R P ≅ S be bimodule equivalences.
Write U for the normalized R-valued contraction obtained from u and w.
For q, q′ ∈ Q and p, p′ ∈ P, the S-valued contraction satisfies
w([q ⊗ p]) w([q′ ⊗ p′]) =
w([q ⊗ (U([p ⊗ q′]) • p′)]).
The R-valued contraction acts on p′ on the left. -/
theorem normalizedS_pair_mul (q : Q) (p : P) (q' : Q) (p' : P) :
    w (mk ℤ R Q P q p) * w (mk ℤ R Q P q' p') =
      w (mk ℤ R Q P q (U (mk ℤ S P Q p q') • p')) := by
  let := rightModule ℤ R S Q P
  calc
    _ = w (op (w (mk ℤ R Q P q' p')) • mk ℤ R Q P q p) :=
      (w.map_smul (op (w (mk ℤ R Q P q' p'))) (mk ℤ R Q P q p)).symm
    _ = w (mk ℤ R Q P q (op (w (mk ℤ R Q P q' p')) • p)) :=
      congrArg w (rightModule_smul_mk ℤ R S Q P _ q p)
    _ = _ := congrArg (fun x : P => w (mk ℤ R Q P q x))
      (normalized_p R S P Q u hu w hw p q' p')

include u hu w hw in
/-- Let R and S be rings, P an R–S bimodule and Q an S–R bimodule,
with commuting actions on additive commutative groups.
Let u : P ⊗_S Q ≅ R and w : Q ⊗_R P ≅ S be bimodule equivalences.
Write U for the normalized R-valued contraction obtained from u and w.
Let J consist of pairs (p_j, q_j) whose pure sum is U⁻¹(1), and K of
pairs (q_k, p_k) whose pure sum is w⁻¹(1). These are finite support types.
For a^R_(j,k) = U([p_k ⊗ q_j]) and b^R_(j,k) = U([p_j ⊗ q_k]),
the ordered unit sum is ∑_(j,k)∈J×K b^R_(j,k) a^R_(j,k) = 1_R. -/
theorem compositeR_unit :
    (∑ i : compositeIndex R S P Q u w hw,
      compositeRRight R S P Q u w hw i * compositeRLeft R S P Q u w hw i) = 1 := by
  classical
  have hK : (∑ k : K, w (mk ℤ R Q P k.val.1 k.val.2)) = 1 :=
    unitSupport_sum_fintype S R Q P w
  have hJ : (∑ j : J, U (mk ℤ S P Q j.val.1 j.val.2)) = 1 :=
    unitSupport_sum_fintype R S P Q U
  change (∑ i : J × K,
    U (mk ℤ S P Q i.1.val.1 i.2.val.1) *
      U (mk ℤ S P Q i.2.val.2 i.1.val.2)) = 1
  rw [Fintype.sum_prod_type]
  simp only [normalizedR_pair_mul R S P Q u hu w hw]
  calc
    (∑ j : J, ∑ k : K,
        U (mk ℤ S P Q j.val.1 (w (mk ℤ R Q P k.val.1 k.val.2) • j.val.2))) =
        ∑ j : J, U (mk ℤ S P Q j.val.1
          ((∑ k : K, w (mk ℤ R Q P k.val.1 k.val.2)) • j.val.2)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_smul, map_sum, map_sum]
    _ = ∑ j : J, U (mk ℤ S P Q j.val.1 j.val.2) := by
      simp only [hK, one_smul]
    _ = 1 := hJ

include u hu w hw in
/-- Let R and S be rings, P an R–S bimodule and Q an S–R bimodule,
with commuting actions on additive commutative groups.
Let u : P ⊗_S Q ≅ R and w : Q ⊗_R P ≅ S be bimodule equivalences.
Write U for the normalized R-valued contraction obtained from u and w.
Let J consist of pairs (p_j, q_j) whose pure sum is U⁻¹(1), and K of
pairs (q_k, p_k) whose pure sum is w⁻¹(1). These are finite support types.
For a^S_(j,k) = w([q_j ⊗ p_k]) and b^S_(j,k) = w([q_k ⊗ p_j]),
the ordered unit sum is ∑_(j,k)∈J×K b^S_(j,k) a^S_(j,k) = 1_S. -/
theorem compositeS_unit :
    (∑ i : compositeIndex R S P Q u w hw,
      compositeSRight R S P Q u w hw i * compositeSLeft R S P Q u w hw i) = 1 := by
  classical
  have hJ : (∑ j : J, U (mk ℤ S P Q j.val.1 j.val.2)) = 1 :=
    unitSupport_sum_fintype R S P Q U
  have hK : (∑ k : K, w (mk ℤ R Q P k.val.1 k.val.2)) = 1 :=
    unitSupport_sum_fintype S R Q P w
  change (∑ i : J × K,
    w (mk ℤ R Q P i.2.val.1 i.1.val.1) *
      w (mk ℤ R Q P i.1.val.2 i.2.val.2)) = 1
  rw [Fintype.sum_prod_type_right]
  simp only [normalizedS_pair_mul R S P Q u hu w hw]
  calc
    (∑ k : K, ∑ j : J,
        w (mk ℤ R Q P k.val.1 (U (mk ℤ S P Q j.val.1 j.val.2) • k.val.2))) =
        ∑ k : K, w (mk ℤ R Q P k.val.1
          ((∑ j : J, U (mk ℤ S P Q j.val.1 j.val.2)) • k.val.2)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_smul, map_sum, map_sum]
    _ = ∑ k : K, w (mk ℤ R Q P k.val.1 k.val.2) := by
      simp only [hJ, one_smul]
    _ = 1 := hK

end TensorProduct.Balanced.Morita
