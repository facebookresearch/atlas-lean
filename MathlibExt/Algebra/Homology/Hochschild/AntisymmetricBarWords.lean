/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarEnveloping
public import MathlibExt.LinearAlgebra.TensorPower.Antisymmetrization
public import MathlibExt.LinearAlgebra.TensorPower.Snoc
public import MathlibExt.GroupTheory.Perm.OrderedDeletion

/-!
# Antisymmetric middle words and the bar differential

Let k be a commutative ring and A a commutative unital k-algebra.
Write P_n = A ⊗[k] A^{⊗(n+1)} for the enveloping bar term and
u_n(a) = 1 ⊗ a_0 ⊗ ⋯ ⊗ a_{n-1} ⊗ 1. Its antisymmetric word is
Alt_n(a) = ∑_{π ∈ S_n} sign(π) u_n(a ∘ π).

The interior adjacent faces cancel in this signed sum. The two endpoint
faces give
d_{n+1} Alt_{n+1}(a) =
∑_{i=0}^{n} (−1)^i Δ(a_i) • Alt_n(a with entry i deleted),
where Δ(x) = x ⊗ 1ᵐᵒᵖ − 1 ⊗ xᵐᵒᵖ in E = A ⊗[k] Aᵐᵒᵖ.
Deletion retains the order of the remaining entries. All permutation
signs and deletion signs are integer coefficients.

The exterior antisymmetrization followed by inserting two unit endpoints
has exactly this full signed-permutation value.

Reference: J.-L. Loday, Cyclic Homology, §§1.1 and 3.2.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct
open MulOpposite

universe u v

namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
For a : Fin n → A, the unit-outer bar word is
u_n(a) = 1 ⊗ a_0 ⊗ ⋯ ⊗ a_{n-1} ⊗ 1 ∈ P_n. -/
def unitOuterWord (n : ℕ) (a : Fin n → A) : envelopingBarDegree k A n :=
  (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
Inserting the unit at both ends defines a k-linear map
U_n : A^{⊗n} → P_n, with
U_n(a_0 ⊗ ⋯ ⊗ a_{n-1}) = 1 ⊗ a_0 ⊗ ⋯ ⊗ a_{n-1} ⊗ 1. -/
def unitOuterLinear (n : ℕ) : TensorPower k n A →ₗ[k] A ⊗[k] TensorPower k (n + 1) A :=
  (TensorProduct.mk k A (TensorPower k (n + 1) A) 1).comp
    ((TensorPower.snocEquiv k A n).toLinearMap.comp
      ((TensorProduct.mk k (TensorPower k n A) A).flip 1))

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
For an elementary middle word tprod(a), insertion of the two outer
units has value U_n(tprod(a)) = u_n(a), with all middle entries
in their given order. -/
theorem unitOuterLinear_tprod (n : ℕ) (a : Fin n → A) :
    unitOuterLinear k A n (PiTensorProduct.tprod k a) = unitOuterWord k A n a := by
  change (1 : A) ⊗ₜ[k]
    TensorPower.snocEquiv k A n (PiTensorProduct.tprod k a ⊗ₜ[k] (1 : A)) = _
  rw [TensorPower.snocEquiv_tmul]
  rfl

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
The antisymmetric bar word on a : Fin n → A is
Alt_n(a) = ∑_{π ∈ S_n} sign(π) u_n(a ∘ π).
Each permutation appears with its integer sign. -/
def antisymmetricBarWord (n : ℕ) (a : Fin n → A) : envelopingBarDegree k A n :=
  ∑ π : Equiv.Perm (Fin n), (Equiv.Perm.sign π : ℤ) • unitOuterWord k A n (a ∘ π)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
For a : Fin n → A, apply exterior antisymmetrization to
 a_0 ∧ ⋯ ∧ a_{n-1} and then insert two outer units. The result is
Alt_n(a) = ∑_{π ∈ S_n} sign(π) u_n(a ∘ π). -/
theorem unitOuterLinear_exteriorAntisymmetrization (n : ℕ) (a : Fin n → A) :
    unitOuterLinear k A n
      (TensorPower.exteriorAntisymmetrization k A n (exteriorPower.ιMulti k n a)) =
      antisymmetricBarWord k A n a := by
  rw [TensorPower.exteriorAntisymmetrization_ιMulti, map_sum]
  apply Finset.sum_congr rfl
  intro π _
  change unitOuterLinear k A n ((Equiv.Perm.sign π : ℤ) • PiTensorProduct.tprod k (a ∘ π)) = _
  rw [map_zsmul, unitOuterLinear_tprod]
  rfl

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
The outer-difference element attached to a ∈ A is
Δ(a) = a ⊗ 1ᵐᵒᵖ − 1 ⊗ aᵐᵒᵖ ∈ E.
Its action is left multiplication by a on the first bar factor minus
right multiplication by a on the last factor. -/
def outerDifference (a : A) : EnvelopingAlgebra k A :=
  a ⊗ₜ[k] op (1 : A) - (1 : A) ⊗ₜ[k] op a

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
The left outer operator acts on a unit-outer word by
(l ⊗ 1ᵐᵒᵖ) • u_n(a) = l ⊗ a_0 ⊗ ⋯ ⊗ a_{n-1} ⊗ 1. -/
theorem unitOuterWord_left (n : ℕ) (l : A) (a : Fin n → A) :
    (l ⊗ₜ[k] op (1 : A)) • unitOuterWord k A n a =
      l ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1) := by
  change TensorPower.outerRepresentation k A n (l ⊗ₜ[k] op (1 : A))
    ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1)) = _
  have hact :
      (letI := TensorPower.outerModule k A n
       (l ⊗ₜ[k] op (1 : A)) • ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1))) =
      TensorPower.outerRepresentation k A n (l ⊗ₜ[k] op (1 : A))
        ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1)) := rfl
  have ht := TensorPower.outerModule_tprod k A n l 1 1 (Fin.snoc a 1)
  exact hact.symm.trans (by
    simpa only [mul_one, one_mul, Fin.init_snoc, Fin.snoc_last] using ht)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
The right outer operator acts on a unit-outer word by
(1 ⊗ rᵐᵒᵖ) • u_n(a) = 1 ⊗ a_0 ⊗ ⋯ ⊗ a_{n-1} ⊗ r. -/
theorem unitOuterWord_right (n : ℕ) (r : A) (a : Fin n → A) :
    ((1 : A) ⊗ₜ[k] op r) • unitOuterWord k A n a =
      (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a r) := by
  change TensorPower.outerRepresentation k A n ((1 : A) ⊗ₜ[k] op r)
    ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1)) = _
  have hact :
      (letI := TensorPower.outerModule k A n
       ((1 : A) ⊗ₜ[k] op r) • ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1))) =
      TensorPower.outerRepresentation k A n ((1 : A) ⊗ₜ[k] op r)
        ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1)) := rfl
  have ht := TensorPower.outerModule_tprod k A n 1 r 1 (Fin.snoc a 1)
  exact hact.symm.trans (by
    simpa only [mul_one, one_mul, Fin.init_snoc, Fin.snoc_last] using ht)

variable {A}

omit [CommRing A] in
private theorem dropFirst_snoc (n : ℕ) (a : Fin (n + 1) → A) (c : A) :
    hochschildDropFirst (Fin.snoc a c) = Fin.snoc (Fin.tail a) c := by
  funext i
  refine Fin.lastCases
    (motive := fun t : Fin (n + 1) =>
      hochschildDropFirst (Fin.snoc (α := fun _ : Fin (n + 2) => A) a c) t =
        Fin.snoc (α := fun _ : Fin (n + 1) => A) (Fin.tail a) c t)
    ?_ (fun j => ?_) i
  · simp only [hochschildDropFirst, Fin.succ_last, Fin.snoc_last]
  · simp only [hochschildDropFirst, Fin.tail, Fin.succ_castSucc, Fin.snoc_castSucc]

private theorem mulAdjacent_lt {n : ℕ} (i j : Fin n) (a : Fin (n + 1) → A) (h : j < i) :
    hochschildMulAdjacent i a j = a j.castSucc := by
  rw [hochschildMulAdjacent, if_neg (ne_of_lt h), Fin.succAbove_succ_of_le i j (le_of_lt h)]

private theorem mulAdjacent_eq {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) :
    hochschildMulAdjacent i a i = a i.castSucc * a i.succ := by
  rw [hochschildMulAdjacent, if_pos rfl]

private theorem mulAdjacent_gt {n : ℕ} (i j : Fin n) (a : Fin (n + 1) → A) (h : i < j) :
    hochschildMulAdjacent i a j = a j.succ := by
  rw [hochschildMulAdjacent, if_neg (ne_of_gt h), Fin.succAbove_succ_of_lt i j h]

private theorem mulAdjacent_snoc_last (n : ℕ) (a : Fin (n + 1) → A) :
    hochschildMulAdjacent (Fin.last n) (Fin.snoc a (1 : A)) = a := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [mulAdjacent_eq]
    simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, mul_one]
  · rw [mulAdjacent_lt (Fin.last n) j.castSucc _
      (by simpa only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] using j.isLt)]
    simp only [Fin.snoc_castSucc]

variable (A)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
For a : Fin(n+1) → A, the first adjacent face of the unit-outer
word satisfies δ_0 u_{n+1}(a) = (a_0 ⊗ 1ᵐᵒᵖ) • u_n(tail(a)).
It multiplies the initial unit by the first middle entry. -/
theorem unitOuterWord_first_face (n : ℕ) (a : Fin (n + 1) → A) :
    (NonUnital.regularFace k A (n + 1) 0).hom (unitOuterWord k A (n + 1) a) =
      (a 0 ⊗ₜ[k] op (1 : A)) • unitOuterWord k A n (Fin.tail a) := by
  calc
    _ = a 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc (Fin.tail a) 1) := by
      rw [unitOuterWord, NonUnital.regularFace_first_tprod, one_mul, dropFirst_snoc]
      rfl
    _ = _ := (unitOuterWord_left k A n (a 0) (Fin.tail a)).symm

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
For a : Fin(n+1) → A, the last adjacent face satisfies
δ_{n+1} u_{n+1}(a) = (1 ⊗ a_nᵐᵒᵖ) • u_n(init(a)).
It multiplies the last middle entry by the terminal unit. -/
theorem unitOuterWord_last_face (n : ℕ) (a : Fin (n + 1) → A) :
    (NonUnital.regularFace k A (n + 1) (Fin.last n).castSucc.succ).hom
      (unitOuterWord k A (n + 1) a) =
      ((1 : A) ⊗ₜ[k] op (a (Fin.last n))) • unitOuterWord k A n (Fin.init a) := by
  calc
    _ = (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k a := by
      rw [unitOuterWord, NonUnital.regularFace_inner_tprod, mulAdjacent_snoc_last]
    _ = _ := by
      rw [unitOuterWord_right, Fin.snoc_init_self]

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
For a : Fin(n+1) → A and 0 ≤ i < n, the interior face
δ_{i+1} of u_{n+1}(a) multiplies a_i and a_{i+1} in the middle
word, retaining the initial and terminal units and the order of every
other entry. -/
theorem unitOuterWord_inner_face (n : ℕ) (i : Fin n) (a : Fin (n + 1) → A) :
    (NonUnital.regularFace k A (n + 1) i.castSucc.castSucc.succ).hom
      (unitOuterWord k A (n + 1) a) =
      (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k
        (hochschildMulAdjacent i.castSucc (Fin.snoc a 1)) :=
  NonUnital.regularFace_inner_tprod k A (n + 1) i.castSucc 1 (Fin.snoc a 1)

variable {A}

private theorem adjacent_swap_snoc (n : ℕ) (i : Fin n) (a : Fin (n + 1) → A) :
    hochschildMulAdjacent i.castSucc
      (Fin.snoc (a ∘ Equiv.swap i.castSucc i.succ) 1) =
      hochschildMulAdjacent i.castSucc (Fin.snoc a 1) := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have hi : i.castSucc < Fin.last n := by
      simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_last] using i.isLt
    rw [mulAdjacent_gt _ _ _ hi, mulAdjacent_gt _ _ _ hi]
    simp only [Fin.succ_last, Fin.snoc_last]
  · rcases lt_trichotomy j i with h | h | h
    · have hi : j.castSucc < i.castSucc := by simpa only [Fin.lt_def, Fin.val_castSucc] using h
      rw [mulAdjacent_lt _ _ _ hi, mulAdjacent_lt _ _ _ hi]
      simp only [Fin.snoc_castSucc, Function.comp_apply]
      rw [Equiv.swap_apply_of_ne_of_ne]
      all_goals
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_castSucc, Fin.val_succ] at hv
        omega
    · subst j
      rw [mulAdjacent_eq, mulAdjacent_eq]
      simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Function.comp_apply,
        Equiv.swap_apply_left, Equiv.swap_apply_right]
      exact mul_comm (a i.succ) (a i.castSucc)
    · have hi : i.castSucc < j.castSucc := by simpa only [Fin.lt_def, Fin.val_castSucc] using h
      rw [mulAdjacent_gt _ _ _ hi, mulAdjacent_gt _ _ _ hi]
      simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Function.comp_apply]
      rw [Equiv.swap_apply_of_ne_of_ne]
      all_goals
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_castSucc, Fin.val_succ] at hv
        omega

variable (A)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
For a : Fin(n+1) → A and 0 ≤ i < n,
∑_{π ∈ S_{n+1}} sign(π) δ_{i+1} u_{n+1}(a ∘ π) = 0.
Pairing permutations by the adjacent transposition cancels the terms
because A is commutative. -/
theorem antisymmetricBarWord_inner_faces (n : ℕ) (i : Fin n) (a : Fin (n + 1) → A) :
    ∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) •
      (NonUnital.regularFace k A (n + 1) i.castSucc.castSucc.succ).hom
        (unitOuterWord k A (n + 1) (a ∘ π)) = 0 := by
  classical
  let τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i.castSucc i.succ
  have hij : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hface (π : Equiv.Perm (Fin (n + 1))) :
      (NonUnital.regularFace k A (n + 1) i.castSucc.castSucc.succ).hom
        (unitOuterWord k A (n + 1) (a ∘ (π * τ : Equiv.Perm (Fin (n + 1))))) =
      (NonUnital.regularFace k A (n + 1) i.castSucc.castSucc.succ).hom
        (unitOuterWord k A (n + 1) (a ∘ π)) := by
    rw [unitOuterWord_inner_face, unitOuterWord_inner_face]
    have hcomp : a ∘ (π * τ : Equiv.Perm (Fin (n + 1))) = (a ∘ π) ∘ τ := by
      funext j
      simp only [Function.comp_apply, Equiv.Perm.mul_apply]
    rw [hcomp]
    rw [adjacent_swap_snoc]
  have hsign (π : Equiv.Perm (Fin (n + 1))) : ((π * τ).sign : ℤ) = -(π.sign : ℤ) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
    simp only [Units.val_mul, Units.val_neg, Units.val_one, mul_neg_one]
  apply Finset.sum_involution (fun π _ => π * τ)
  · intro π _
    rw [hsign, hface, neg_smul]
    exact add_neg_cancel ((π.sign : ℤ) •
      (NonUnital.regularFace k A (n + 1) i.castSucc.castSucc.succ).hom
        (unitOuterWord k A (n + 1) (a ∘ π)))
  · intro π _ _ h
    have hv := congrArg (fun p : Equiv.Perm (Fin (n + 1)) => p i.castSucc) h
    simp only [Equiv.Perm.mul_apply, τ, Equiv.swap_apply_left] at hv
    exact hij (π.injective hv.symm)
  · intro π _
    exact Finset.mem_univ _
  · intro π _
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]

variable {A}

omit [CommRing A] in
private theorem orderedFirst_tail (n : ℕ) (a : Fin (n + 1) → A)
    (i : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    Fin.tail (a ∘ Equiv.Perm.orderedFirst i π) = (a ∘ i.succAbove) ∘ π := by
  ext j
  simp only [Fin.tail, Function.comp_apply, Equiv.Perm.orderedFirst_succ]

omit [CommRing A] in
private theorem orderedLast_init (n : ℕ) (a : Fin (n + 1) → A)
    (i : Fin (n + 1)) (π : Equiv.Perm (Fin n)) :
    Fin.init (a ∘ Equiv.Perm.orderedLast i π) = (a ∘ i.succAbove) ∘ π := by
  ext j
  simp only [Fin.init, Function.comp_apply, Equiv.Perm.orderedLast_castSucc]

variable (A)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
The signed sum of the first faces is
∑_{π ∈ S_{n+1}} sign(π) δ_0 u_{n+1}(a ∘ π) =
∑_{i=0}^{n} (−1)^i (a_i ⊗ 1ᵐᵒᵖ) • Alt_n(a with entry i deleted).
The remaining entries stay in their given order. -/
theorem antisymmetricBarWord_first_faces (n : ℕ) (a : Fin (n + 1) → A) :
    ∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) •
      (NonUnital.regularFace k A (n + 1) 0).hom
        (unitOuterWord k A (n + 1) (a ∘ π)) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        ((a i ⊗ₜ[k] op (1 : A)) • antisymmetricBarWord k A n (a ∘ i.succAbove)) := by
  rw [Equiv.Perm.sum_orderedFirst n]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Equiv.Perm.sign_orderedFirst_int, unitOuterWord_first_face,
    Function.comp_apply, Equiv.Perm.orderedFirst_zero, orderedFirst_tail,
    antisymmetricBarWord, mul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro π _
  have hf := unitOuterWord_first_face k A n (a ∘ Equiv.Perm.orderedFirst i π)
  simp only [Function.comp_apply, Equiv.Perm.orderedFirst_zero, orderedFirst_tail] at hf
  exact (congrArg (fun x : envelopingBarDegree k A n =>
    (-1 : ℤ) ^ i.val • (π.sign : ℤ) • x) hf).trans
      (congrArg (fun x : envelopingBarDegree k A n => (-1 : ℤ) ^ i.val • x)
        (smul_comm (π.sign : ℤ) (a i ⊗ₜ[k] op (1 : A))
          (unitOuterWord k A n ((a ∘ i.succAbove) ∘ π))))

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
The signed sum of the last adjacent faces, before the boundary sign
of that face is applied, is
∑_{π ∈ S_{n+1}} sign(π) δ_{n+1} u_{n+1}(a ∘ π) =
(−1)^n ∑_{i=0}^{n} (−1)^i (1 ⊗ a_iᵐᵒᵖ) • Alt_n(a with entry i deleted). -/
theorem antisymmetricBarWord_last_faces (n : ℕ) (a : Fin (n + 1) → A) :
    ∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) •
      (NonUnital.regularFace k A (n + 1) (Fin.last n).castSucc.succ).hom
        (unitOuterWord k A (n + 1) (a ∘ π)) =
      (-1 : ℤ) ^ n • ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        (((1 : A) ⊗ₜ[k] op (a i)) • antisymmetricBarWord k A n (a ∘ i.succAbove)) := by
  rw [Equiv.Perm.sum_orderedLast n, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Equiv.Perm.sign_orderedLast_int, unitOuterWord_last_face,
    Function.comp_apply, Equiv.Perm.orderedLast_last, orderedLast_init,
    antisymmetricBarWord, mul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro π _
  have hf := unitOuterWord_last_face k A n (a ∘ Equiv.Perm.orderedLast i π)
  simp only [Function.comp_apply, Equiv.Perm.orderedLast_last, orderedLast_init] at hf
  exact (congrArg (fun x : envelopingBarDegree k A n =>
    (-1 : ℤ) ^ n • (-1 : ℤ) ^ i.val • (π.sign : ℤ) • x) hf).trans
      (congrArg (fun x : envelopingBarDegree k A n =>
        (-1 : ℤ) ^ n • (-1 : ℤ) ^ i.val • x)
        (smul_comm (π.sign : ℤ) ((1 : A) ⊗ₜ[k] op (a i))
          (unitOuterWord k A n ((a ∘ i.succAbove) ∘ π))))

private theorem negOnePow_double (n : ℕ) : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n hn =>
    calc
      _ = ((-1 : ℤ) ^ n * (-1)) * ((-1 : ℤ) ^ n * (-1)) := by rw [pow_succ]
      _ = (-1 : ℤ) ^ n * (-1 : ℤ) ^ n := by ring
      _ = 1 := hn

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Write E = A ⊗[k] Aᵐᵒᵖ and P_n = A ⊗[k] A^{⊗(n+1)}
with the outer left E-action.
Put Δ(x) = x ⊗ 1ᵐᵒᵖ − 1 ⊗ xᵐᵒᵖ. The full bar boundary
on an antisymmetric word is
 d_{n+1} Alt_{n+1}(a) =
∑_{i=0}^{n} (−1)^i Δ(a_i) • Alt_n(a with entry i deleted).
Each deletion preserves the order of the remaining middle entries. -/
theorem antisymmetricBarWord_boundary (n : ℕ) (a : Fin (n + 1) → A) :
    ((envelopingBar k A).d (n + 1) n).hom (antisymmetricBarWord k A (n + 1) a) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        (outerDifference k A (a i) • antisymmetricBarWord k A n (a ∘ i.succAbove)) := by
  have hd (b : Fin (n + 1) → A) :
      ((envelopingBar k A).d (n + 1) n).hom (unitOuterWord k A (n + 1) b) =
        (NonUnital.regularFace k A (n + 1) 0).hom (unitOuterWord k A (n + 1) b) +
        (∑ j : Fin n, (-1 : ℤ) ^ (j.val + 1) •
          (NonUnital.regularFace k A (n + 1) j.castSucc.castSucc.succ).hom
            (unitOuterWord k A (n + 1) b)) +
        (-1 : ℤ) ^ (n + 1) •
          (NonUnital.regularFace k A (n + 1) (Fin.last n).castSucc.succ).hom
            (unitOuterWord k A (n + 1) b) := by
    let z : NonUnital.chainLevel k A A (n + 2) := unitOuterWord k A (n + 1) b
    have hsum := congrArg
      (fun d : NonUnital.chainLevel k A A (n + 2) ⟶
        NonUnital.chainLevel k A A (n + 1) => d.hom z) (underlyingBar_d k A n)
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
      LinearMap.smul_apply] at hsum
    have hstart : ((envelopingBar k A).d (n + 1) n).hom
        (unitOuterWord k A (n + 1) b) =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          (NonUnital.regularFace k A (n + 1) i.castSucc).hom z :=
      (envelopingBar_d_apply k A n (unitOuterWord k A (n + 1) b)).trans hsum
    refine hstart.trans ?_
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
      pow_zero, one_smul, Fin.castSucc_zero]
    abel
  have hinter :
      ∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) •
        (∑ j : Fin n, (-1 : ℤ) ^ (j.val + 1) •
          (NonUnital.regularFace k A (n + 1) j.castSucc.castSucc.succ).hom
            (unitOuterWord k A (n + 1) (a ∘ π))) = 0 := by
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    calc
      _ = ∑ π : Equiv.Perm (Fin (n + 1)), (-1 : ℤ) ^ (j.val + 1) •
          ((π.sign : ℤ) •
            (NonUnital.regularFace k A (n + 1) j.castSucc.castSucc.succ).hom
              (unitOuterWord k A (n + 1) (a ∘ π))) := by
        apply Finset.sum_congr rfl
        intro π _
        exact smul_comm _ _ _
      _ = 0 := by
        rw [← Finset.smul_sum, antisymmetricBarWord_inner_faces, smul_zero]
  let D : (envelopingBarDegree k A (n + 1)).carrier →ₗ[EnvelopingAlgebra k A]
      (envelopingBarDegree k A n).carrier := ((envelopingBar k A).d (n + 1) n).hom
  have hstart : D (antisymmetricBarWord k A (n + 1) a) =
      ∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) •
        D (unitOuterWord k A (n + 1) (a ∘ π)) := by
    change D (∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) •
      unitOuterWord k A (n + 1) (a ∘ π)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro π _
    exact map_zsmul D _ _
  have hd' (b : Fin (n + 1) → A) :
      D (unitOuterWord k A (n + 1) b) =
        (NonUnital.regularFace k A (n + 1) 0).hom (unitOuterWord k A (n + 1) b) +
        (∑ j : Fin n, (-1 : ℤ) ^ (j.val + 1) •
          (NonUnital.regularFace k A (n + 1) j.castSucc.castSucc.succ).hom
            (unitOuterWord k A (n + 1) b)) +
        (-1 : ℤ) ^ (n + 1) •
          (NonUnital.regularFace k A (n + 1) (Fin.last n).castSucc.succ).hom
            (unitOuterWord k A (n + 1) b) := hd b
  let F (π : Equiv.Perm (Fin (n + 1))) : envelopingBarDegree k A n :=
    (NonUnital.regularFace k A (n + 1) 0).hom
      (unitOuterWord k A (n + 1) (a ∘ π))
  let I (π : Equiv.Perm (Fin (n + 1))) : envelopingBarDegree k A n :=
    ∑ j : Fin n, (-1 : ℤ) ^ (j.val + 1) •
      (NonUnital.regularFace k A (n + 1) j.castSucc.castSucc.succ).hom
        (unitOuterWord k A (n + 1) (a ∘ π))
  let V (π : Equiv.Perm (Fin (n + 1))) : envelopingBarDegree k A n :=
    (NonUnital.regularFace k A (n + 1) (Fin.last n).castSucc.succ).hom
      (unitOuterWord k A (n + 1) (a ∘ π))
  let L (π : Equiv.Perm (Fin (n + 1))) : envelopingBarDegree k A n :=
    (-1 : ℤ) ^ (n + 1) • V π
  have hdist :
      (∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) • (F π + I π + L π)) =
        (∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) • F π) +
        (∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) • I π) +
        (∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) • L π) := by
    simp only [smul_add, Finset.sum_add_distrib]
  have hvalues :
      (∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) •
        D (unitOuterWord k A (n + 1) (a ∘ π))) =
        ∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) • (F π + I π + L π) := by
    apply Finset.sum_congr rfl
    intro π _
    exact congrArg (fun x : envelopingBarDegree k A n => (π.sign : ℤ) • x) (hd' (a ∘ π))
  have hI : (∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) • I π) = 0 := hinter
  refine hstart.trans ((hvalues.trans hdist).trans ?_)
  rw [hI, add_zero]
  have hlast :
      (∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) • L π) =
        -∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
          (((1 : A) ⊗ₜ[k] op (a i)) • antisymmetricBarWord k A n (a ∘ i.succAbove)) := by
    have hcomm :
        (∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) • L π) =
          (-1 : ℤ) ^ (n + 1) •
            ∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) • V π := by
      change (∑ π : Equiv.Perm (Fin (n + 1)),
        (π.sign : ℤ) • ((-1 : ℤ) ^ (n + 1) • V π)) = _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro π _
      exact smul_comm _ _ _
    have hV : (∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) • V π) =
        (-1 : ℤ) ^ n • ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
          (((1 : A) ⊗ₜ[k] op (a i)) • antisymmetricBarWord k A n (a ∘ i.succAbove)) :=
      antisymmetricBarWord_last_faces k A n a
    rw [hcomm, hV, ← mul_smul]
    rw [pow_succ]
    have hpow : ((-1 : ℤ) ^ n * (-1)) * (-1 : ℤ) ^ n = -1 := by
      calc
        _ = -((-1 : ℤ) ^ n * (-1 : ℤ) ^ n) := by ring
        _ = -1 := by rw [negOnePow_double]
    rw [hpow, neg_one_smul]
  have hF : (∑ π : Equiv.Perm (Fin (n + 1)), (π.sign : ℤ) • F π) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        ((a i ⊗ₜ[k] op (1 : A)) • antisymmetricBarWord k A n (a ∘ i.succAbove)) :=
    antisymmetricBarWord_first_faces k A n a
  rw [hF, hlast]
  simp only [outerDifference, sub_smul, smul_sub, Finset.sum_sub_distrib]
  abel

end ModuleCat.Algebra.Hochschild.AdjacentBar
