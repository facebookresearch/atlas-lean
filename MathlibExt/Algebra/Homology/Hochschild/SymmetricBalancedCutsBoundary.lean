/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricBalancedCuts
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The signed boundary formula for A-balanced deconcatenation

Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module. At p+q=n,
deconcatenation Dₚ,ᵩ sends a degree-n coefficient word to an A-balanced pair. Its boundary
formula is Dₚ,ᵩ bₙ = (bₚ ⊗ id)Dₚ₊₁,ᵩ + (-1)ᵖ(id ⊗ bᵩ)Dₚ,ᵩ₊₁. The first boundary acts on the
regular coefficient ULift A. The two middle head terms cancel because A-balancing identifies
their values and their integer signs are opposite.

For the Hochschild differential and tensor signs, see J.-L. Loday, Cyclic Homology, 2nd ed.,
Chapter 1 and §4.5.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- Deconcatenation with an explicit target-degree equality.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, p+q=n gives Dₚ,ᵩ : M ⊗[k] A⊗n → (ULift A ⊗[k] A⊗p) ⊗[A] (M ⊗[k] A⊗q), preserving the
stated degree equality. -/
def algebraDeconcatCutAt (p q n : ℕ) (h : p + q = n) :
    M ⊗[k] TensorPower k n A →ₗ[A]
      (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[A] (M ⊗[k] TensorPower k q A) :=
  (algebraDeconcatCut k A M p q).comp
    (TensorProduct.AlgebraTensorModule.lTensor A M
      (TensorPower.cast k A h).symm.toLinearMap)

/-- Explicit-degree deconcatenation at the sum p+q.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, using n=p+q and its reflexive equality recovers algebraDeconcatCut(p,q). -/
@[simp]
lemma algebraDeconcatCutAt_refl (p q : ℕ) :
    algebraDeconcatCutAt k A M p q (p + q) rfl = algebraDeconcatCut k A M p q := by
  rw [algebraDeconcatCutAt, TensorPower.cast_refl]
  change (algebraDeconcatCut k A M p q).comp
    (TensorProduct.AlgebraTensorModule.lTensor A M (LinearMap.id : TensorPower k (p + q) A →ₗ[k]
      TensorPower k (p + q) A)) = algebraDeconcatCut k A M p q
  rw [TensorProduct.AlgebraTensorModule.lTensor_id, LinearMap.comp_id]

/-- Deconcatenation of a degree-cast appended tensor word.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, an appended p-word and q-word transported along p+q=n splits into (ULift.up(1_A) ⊗
tprod(x)) ⊗[A] (m ⊗ tprod(y)), retaining both word orders. -/
lemma algebraDeconcatCutAt_tprod (p q n : ℕ) (h : p + q = n)
    (m : M) (x : Fin p → A) (y : Fin q → A) :
    algebraDeconcatCutAt k A M p q n h
        (m ⊗ₜ[k] PiTensorProduct.tprod k (Fin.append x y ∘ Fin.cast h.symm)) =
      (ULift.up (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k x) ⊗ₜ[A]
        (m ⊗ₜ[k] PiTensorProduct.tprod k y) := by
  subst n
  simpa only [algebraDeconcatCutAt_refl, Fin.cast_refl, Function.comp_id] using
    algebraDeconcatCut_tprod k A M p q m x y

section TupleFaces

variable {A}

/-- On the first p+1 positions, append(x,cons(c,y)) agrees with snoc(x,c). -/
private lemma pivotWord_left {p q : ℕ} (x : Fin p → A) (c : A) (y : Fin q → A)
    (i : Fin (p + 1)) :
    Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) (Fin.castLE (by omega : p + 1 ≤ p + (q + 1)) i) =
      Fin.snoc (n := p) (α := fun _ => A) x c i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hi : Fin.castLE (by omega : p + 1 ≤ p + (q + 1)) (Fin.last p) =
        Fin.natAdd p (0 : Fin (q + 1)) := Fin.ext rfl
    rw [hi, Fin.append_right, Fin.cons_zero, Fin.snoc_last]
  · have hi : Fin.castLE (by omega : p + 1 ≤ p + (q + 1)) j.castSucc =
        Fin.castAdd (q + 1) j := Fin.ext rfl
    rw [hi, Fin.append_left, Fin.snoc_castSucc]

private lemma mulAdjacent_lt {n : ℕ} (i j : Fin n) (a : Fin (n + 1) → A) (h : j < i) :
    hochschildMulAdjacent i a j = a j.castSucc := by
  rw [hochschildMulAdjacent, if_neg (ne_of_lt h),
    Fin.succAbove_succ_of_le i j (le_of_lt h)]

private lemma mulAdjacent_eq {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) :
    hochschildMulAdjacent i a i = a i.castSucc * a i.succ := by
  rw [hochschildMulAdjacent, if_pos rfl]

private lemma mulAdjacent_gt {n : ℕ} (i j : Fin n) (a : Fin (n + 1) → A) (h : i < j) :
    hochschildMulAdjacent i a j = a j.succ := by
  rw [hochschildMulAdjacent, if_neg (ne_of_gt h), Fin.succAbove_succ_of_lt i j h]

/-- Removing the first entry of append(x,cons(c,y)) removes the first entry of snoc(x,c). -/
private lemma dropFirst_pivotWord {p q : ℕ} (x : Fin p → A) (c : A) (y : Fin q → A) :
    hochschildDropFirst (n := p + q) (Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)) =
      Fin.append (hochschildDropFirst (n := p) (Fin.snoc (n := p) (α := fun _ => A) x c)) y := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]
    change Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)
      (Fin.castLE (by omega : p + 1 ≤ p + (q + 1)) i.succ) = Fin.snoc (n := p) (α := fun _ => A) x c i.succ
    exact pivotWord_left x c y i.succ
  · rw [Fin.append_right]
    change Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) (Fin.natAdd p i.succ) = y i
    rw [Fin.append_right, Fin.cons_succ]

/-- Removing the last entry of append(x,cons(c,y)) removes the last entry of cons(c,y). -/
private lemma dropLast_pivotWord {p q : ℕ} (x : Fin p → A) (c : A) (y : Fin q → A) :
    hochschildDropLast (n := p + q) (Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)) =
      Fin.append x (hochschildDropLast (n := q) (Fin.cons (n := q) (α := fun _ => A) c y)) := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]
    change Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) (Fin.castAdd (q + 1) i) = x i
    exact Fin.append_left x (Fin.cons (n := q) (α := fun _ => A) c y) i
  · rw [Fin.append_right]
    change Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) (Fin.natAdd p i.castSucc) = Fin.cons (n := q) (α
          := fun _ => A) c y i.castSucc
    exact Fin.append_right x (Fin.cons (n := q) (α := fun _ => A) c y) i.castSucc

/-- An interior face in the left block multiplies adjacent entries of snoc(x,c). -/
private lemma mulAdjacent_pivotWord_left {p q : ℕ} (x : Fin p → A) (c : A) (y : Fin q → A)
    (i : Fin p) :
    hochschildMulAdjacent (n := p + q) (Fin.castAdd q i) (Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)) =
      Fin.append (hochschildMulAdjacent (n := p) i (Fin.snoc (n := p) (α := fun _ => A) x c)) y := by
  ext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.append_left]
    rcases lt_trichotomy j i with h | h | h
    · rw [mulAdjacent_lt _ _ _ (by simpa only [Fin.lt_def, Fin.val_castAdd] using h),
        mulAdjacent_lt i j _ h]
      change Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)
        (Fin.castLE (by omega : p + 1 ≤ p + (q + 1)) j.castSucc) = Fin.snoc (n := p) (α := fun _ => A) x c j.castSucc
      exact pivotWord_left x c y j.castSucc
    · subst j
      rw [mulAdjacent_eq, mulAdjacent_eq]
      change Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)
          (Fin.castLE (by omega : p + 1 ≤ p + (q + 1)) i.castSucc) *
        Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)
          (Fin.castLE (by omega : p + 1 ≤ p + (q + 1)) i.succ) = _
      rw [pivotWord_left, pivotWord_left]
    · rw [mulAdjacent_gt _ _ _ (by simpa only [Fin.lt_def, Fin.val_castAdd] using h),
        mulAdjacent_gt i j _ h]
      change Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)
        (Fin.castLE (by omega : p + 1 ≤ p + (q + 1)) j.succ) = Fin.snoc (n := p) (α := fun _ => A) x c j.succ
      exact pivotWord_left x c y j.succ
  · rw [Fin.append_right]
    have h : Fin.castAdd q i < Fin.natAdd p j := by
      change i.val < p + j.val
      omega
    rw [mulAdjacent_gt _ _ _ h]
    change Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) (Fin.natAdd p j.succ) = y j
    rw [Fin.append_right, Fin.cons_succ]

/-- An interior face in the right block multiplies adjacent entries of cons(c,y). -/
private lemma mulAdjacent_pivotWord_right {p q : ℕ} (x : Fin p → A) (c : A) (y : Fin q → A)
    (i : Fin q) :
    hochschildMulAdjacent (n := p + q) (Fin.natAdd p i) (Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)) =
      Fin.append x (hochschildMulAdjacent (n := q) i (Fin.cons (n := q) (α := fun _ => A) c y)) := by
  ext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.append_left]
    have h : Fin.castAdd q j < Fin.natAdd p i := by
      change j.val < p + i.val
      omega
    rw [mulAdjacent_lt _ _ _ h]
    change Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) (Fin.castAdd (q + 1) j) = x j
    exact Fin.append_left x (Fin.cons (n := q) (α := fun _ => A) c y) j
  · rw [Fin.append_right]
    rcases lt_trichotomy j i with h | h | h
    · rw [mulAdjacent_lt _ _ _ (by
          change p + j.val < p + i.val
          exact Nat.add_lt_add_left h p),
        mulAdjacent_lt i j _ h]
      change Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) (Fin.natAdd p j.castSucc) = Fin.cons (n := q) (α
          := fun _ => A) c y j.castSucc
      exact Fin.append_right x (Fin.cons (n := q) (α := fun _ => A) c y) j.castSucc
    · subst j
      rw [mulAdjacent_eq, mulAdjacent_eq]
      change Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) (Fin.natAdd p i.castSucc) *
        Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) (Fin.natAdd p i.succ) = _
      rw [Fin.append_right, Fin.append_right]
    · rw [mulAdjacent_gt _ _ _ (by
          change p + i.val < p + j.val
          exact Nat.add_lt_add_left h p),
        mulAdjacent_gt i j _ h]
      change Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) (Fin.natAdd p j.succ) = Fin.cons (n := q) (α := fun _ => A) c y j.succ
      exact Fin.append_right x (Fin.cons (n := q) (α := fun _ => A) c y) j.succ

private lemma pivotWord_first {p q : ℕ} (x : Fin p → A) (c : A) (y : Fin q → A) :
    Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) 0 = Fin.snoc (n := p) (α := fun _ => A) x c 0 := by
  simpa only [Fin.castLE_zero] using pivotWord_left x c y (0 : Fin (p + 1))

private lemma pivotWord_last {p q : ℕ} (x : Fin p → A) (c : A) (y : Fin q → A) :
    Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) (Fin.last (p + q)) = Fin.cons (n := q) (α := fun
          _ => A) c y (Fin.last q) := by
  simpa only [Fin.natAdd_last] using Fin.append_right x (Fin.cons (n := q) (α := fun _ => A) c y) (Fin.last q)

private lemma dropLast_snoc {p : ℕ} (x : Fin p → A) (c : A) :
    hochschildDropLast (n := p) (Fin.snoc (n := p) (α := fun _ => A) x c) = x := by
  funext i
  exact Fin.snoc_castSucc (α := fun _ => A) c x i

private lemma dropFirst_cons {q : ℕ} (c : A) (y : Fin q → A) :
    hochschildDropFirst (n := q) (Fin.cons (n := q) (α := fun _ => A) c y) = y := by
  funext i
  exact Fin.cons_succ (α := fun _ => A) c y i

private lemma exists_pivotWord (p q : ℕ) (a : Fin (p + q + 1) → A) :
    ∃ (x : Fin p → A) (c : A) (y : Fin q → A), a = Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) := by
  let x : Fin p → A := fun i => a (Fin.castAdd (q + 1) i)
  let z : Fin (q + 1) → A := fun i => a (Fin.natAdd p i)
  refine ⟨x, z 0, Fin.tail z, ?_⟩
  rw [Fin.cons_self_tail]
  funext i
  refine Fin.addCases (m := p) (n := q + 1) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
  · rw [Fin.append_right]

end TupleFaces

/-- The full signed symmetric Hochschild boundary on a tensor word.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, bₙ(m ⊗ (a₀,…,aₙ)) is a₀m ⊗ (a₁,…,aₙ), plus ∑ᵢ₌₀ⁿ⁻¹ (-1)ⁱ⁺¹ m ⊗ (… ,aᵢaᵢ₊₁,…), plus
(-1)ⁿ⁺¹ aₙm ⊗ (a₀,…,aₙ₋₁). -/
lemma algebraBoundary_tprod_endpoints (n : ℕ) (m : M) (a : Fin (n + 1) → A) :
    algebraBoundary k A M n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ((a 0 • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropFirst a)) +
      (∑ i : Fin n, (-1 : ℤ) ^ (i.val + 1) •
        (m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildMulAdjacent i a))) +
      (-1 : ℤ) ^ (n + 1) •
        ((a (Fin.last n) • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a)) := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  have hboundary := ModuleCat.Algebra.Hochschild.boundary_tprod k A M n m a
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hboundary
  simp only [ModuleCat.Algebra.Hochschild.faceValue, Fin.cases_zero, Fin.cases_succ,
    Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_zero, pow_zero, one_smul,
    Fin.val_succ, Fin.val_castSucc, Fin.val_last, opModule_smul, MulOpposite.unop_op, add_assoc] at hboundary
  have hd := ModuleCat.Algebra.Hochschild.chainComplex_d k A M n
  have hvalue := congrArg
    (fun f : ModuleCat.Algebra.Hochschild.chainLevel k A M (n + 1) ⟶
      ModuleCat.Algebra.Hochschild.chainLevel k A M n =>
        f.hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) hd
  let first : M ⊗[k] TensorPower k n A :=
    (a 0 • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropFirst a)
  let interior : M ⊗[k] TensorPower k n A := ∑ i : Fin n, (-1 : ℤ) ^ (i.val + 1) •
    (m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildMulAdjacent i a))
  let last : M ⊗[k] TensorPower k n A := (-1 : ℤ) ^ (n + 1) •
    ((a (Fin.last n) • m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a))
  have hassoc : first + (interior + last) = (first + interior) + last :=
    (add_assoc first interior last).symm
  exact hvalue.trans (hboundary.trans hassoc)

private lemma ulift_smul_one (a : A) :
    a • (ULift.up (1 : A) : ULift.{w} A) = ULift.up a := by
  apply ULift.ext
  change a * 1 = a
  exact mul_one a

/-- Opposite middle-head signs cancel after A-balancing.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, the terms (-1)ᵖ⁺¹((c ⊗ x) ⊗[A] (m ⊗ y)) and (-1)ᵖ((1_A ⊗ x) ⊗[A] ((c • m) ⊗ y)) sum
to zero. -/
lemma algebraMiddleHead_signed_cancel (p q : ℕ) (c : A) (m : M)
    (x : TensorPower k p A) (y : TensorPower k q A) :
    (-1 : ℤ) ^ (p + 1) • ((ULift.up c ⊗ₜ[k] x) ⊗ₜ[A] (m ⊗ₜ[k] y)) +
      (-1 : ℤ) ^ p • ((ULift.up (1 : A) ⊗ₜ[k] x) ⊗ₜ[A] ((c • m) ⊗ₜ[k] y)) = 0 := by
  rw [algebraMiddleHead_balance, pow_succ, mul_neg_one, neg_smul]
  exact neg_add_cancel _

private lemma algebraDeconcatCutAt_pivot_left (p q : ℕ) (m : M)
    (x : Fin p → A) (c : A) (y : Fin q → A) :
    algebraDeconcatCutAt k A M (p + 1) q (p + q + 1) (by omega)
        (m ⊗ₜ[k] PiTensorProduct.tprod k (Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y))) =
      (ULift.up (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc (n := p) (α := fun _ => A) x c)) ⊗ₜ[A]
        (m ⊗ₜ[k] PiTensorProduct.tprod k y) := by
  have ht : Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y) =
      Fin.append (Fin.snoc (n := p) (α := fun _ => A) x c) y ∘ Fin.cast (show (p + 1) + q = p + q +
        1 by omega).symm := by
    simpa only using Fin.append_right_cons x c y
  rw [ht]
  exact algebraDeconcatCutAt_tprod k A M (p + 1) q (p + q + 1) (by omega) m (Fin.snoc (n := p) (α := fun _ => A) x c) y

private lemma algebraDeconcatCutAt_pivot_right (p q : ℕ) (m : M)
    (x : Fin p → A) (c : A) (y : Fin q → A) :
    algebraDeconcatCutAt k A M p (q + 1) (p + q + 1) (by omega)
        (m ⊗ₜ[k] PiTensorProduct.tprod k (Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y))) =
      (ULift.up (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k x) ⊗ₜ[A]
        (m ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons (n := q) (α := fun _ => A) c y)) := by
  have hcut : algebraDeconcatCutAt k A M p (q + 1) (p + q + 1) (by omega) =
      algebraDeconcatCut k A M p (q + 1) := algebraDeconcatCutAt_refl k A M p (q + 1)
  exact (DFunLike.congr_fun hcut
    (m ⊗ₜ[k] PiTensorProduct.tprod k
      (Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)))).trans
    (algebraDeconcatCut_tprod k A M p (q + 1) m x (Fin.cons (n := q) (α := fun _ => A) c y))

/-- Deconcatenating the full boundary of the pivot word partitions its endpoint and interior faces. -/
private lemma algebraDeconcatCut_boundary_pivot (p q : ℕ) (m : M)
    (x : Fin p → A) (c : A) (y : Fin q → A) :
    algebraDeconcatCut k A M p q
        (algebraBoundary k A M (p + q)
          (m ⊗ₜ[k] PiTensorProduct.tprod k (Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)))) =
      ((ULift.up (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropFirst (n := p) (Fin.snoc (n
        := p) (α := fun _ => A) x c))) ⊗ₜ[A]
        (((Fin.snoc (n := p) (α := fun _ => A) x c 0) • m) ⊗ₜ[k] PiTensorProduct.tprod k y)) +
      (∑ i : Fin p, (-1 : ℤ) ^ (i.val + 1) •
        ((ULift.up (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildMulAdjacent (n := p) i
          (Fin.snoc (n := p) (α := fun _ => A) x c))) ⊗ₜ[A]
          (m ⊗ₜ[k] PiTensorProduct.tprod k y))) +
      (∑ i : Fin q, (-1 : ℤ) ^ (p + i.val + 1) •
        ((ULift.up (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k x) ⊗ₜ[A]
          (m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildMulAdjacent (n := q) i (Fin.cons (n := q) (α
            := fun _ => A) c y))))) +
      (-1 : ℤ) ^ (p + q + 1) •
        ((ULift.up (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k x) ⊗ₜ[A]
          (((Fin.cons (n := q) (α := fun _ => A) c y (Fin.last q)) • m) ⊗ₜ[k]
            PiTensorProduct.tprod k (hochschildDropLast (n := q) (Fin.cons (n := q) (α := fun _ => A) c y)))) := by
  rw [algebraBoundary_tprod_endpoints]
  simp only [map_add, map_sum, map_zsmul]
  rw [dropFirst_pivotWord, dropLast_pivotWord, pivotWord_first, pivotWord_last,
    algebraDeconcatCut_tprod, algebraDeconcatCut_tprod, Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, mulAdjacent_pivotWord_left,
    mulAdjacent_pivotWord_right, algebraDeconcatCut_tprod]
  abel

private lemma add_middle_cancel {T : Type*} [AddCommGroup T]
    (a b c d u v : T) (h : u + v = 0) :
    a + b + c + d = (a + b + u) + (v + c + d) := by
  symm
  calc
    _ = a + b + (u + v) + c + d := by abel
    _ = a + b + c + d := by rw [h, add_zero]

private lemma zsmul_tmul {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y] (s : ℤ) (x : X) (y : Y) :
    (s • x) ⊗ₜ[A] y = s • (x ⊗ₜ[A] y) :=
  (TensorProduct.smul_tmul' s x y).symm

private lemma tmul_zsmul {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y] (s : ℤ) (x : X) (y : Y) :
    x ⊗ₜ[A] (s • y) = s • (x ⊗ₜ[A] y) :=
  TensorProduct.tmul_smul s x y

/-- The deconcatenation boundary formula at an explicit middle vector.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, on the word append(x,cons(c,y)), Dₚ,ᵩ b equals the regular-coefficient boundary of
Dₚ₊₁,ᵩ plus (-1)ᵖ times the M-coefficient boundary of Dₚ,ᵩ₊₁. -/
lemma algebraDeconcatCutAt_boundary_pivot (p q : ℕ) (m : M)
    (x : Fin p → A) (c : A) (y : Fin q → A) :
    algebraDeconcatCutAt k A M p q (p + q) rfl
        (algebraBoundary k A M (p + q)
          (m ⊗ₜ[k] PiTensorProduct.tprod k (Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)))) =
      TensorProduct.map (algebraBoundary k A (ULift.{w} A) p) LinearMap.id
        (algebraDeconcatCutAt k A M (p + 1) q (p + q + 1) (by omega)
          (m ⊗ₜ[k] PiTensorProduct.tprod k (Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)))) +
      (-1 : ℤ) ^ p •
        TensorProduct.map LinearMap.id (algebraBoundary k A M q)
          (algebraDeconcatCutAt k A M p (q + 1) (p + q + 1) (by omega)
            (m ⊗ₜ[k] PiTensorProduct.tprod k (Fin.append (m := p) (n := q + 1) x
        (Fin.cons (n := q) (α := fun _ => A) c y)))) := by
  rw [algebraDeconcatCutAt_refl, algebraDeconcatCut_boundary_pivot,
    algebraDeconcatCutAt_pivot_left, algebraDeconcatCutAt_pivot_right,
    TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.id_apply,
    algebraBoundary_tprod_endpoints, algebraBoundary_tprod_endpoints]
  simp only [TensorProduct.add_tmul, TensorProduct.sum_tmul, zsmul_tmul,
    TensorProduct.tmul_add, TensorProduct.tmul_sum, tmul_zsmul,
    ulift_smul_one, dropLast_snoc, dropFirst_cons, Fin.snoc_last, Fin.cons_zero]
  rw [algebraMiddleHead_balance k A M p q (Fin.snoc (n := p) (α := fun _ => A) x c 0) m
    (PiTensorProduct.tprod k (hochschildDropFirst (n := p) (Fin.snoc (n := p) (α := fun _ => A) x
      c))) (PiTensorProduct.tprod k y)]
  let T := (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[A] (M ⊗[k] TensorPower k q A)
  have hsmul_add (s : ℤ) (a b : T) : s • (a + b) = s • a + s • b := smul_add s a b
  have hsmul_sum (s : ℤ) (f : Fin q → T) : s • (∑ i : Fin q, f i) = ∑ i : Fin q, s • f i := by
    let F : T →+ T :=
      { toFun := fun x => s • x
        map_zero' := smul_zero s
        map_add' := fun x y => hsmul_add s x y }
    exact map_sum F f Finset.univ
  have hsmul_smul (s t : ℤ) (a : T) : s • (t • a) = (s * t) • a := smul_smul s t a
  simp only [hsmul_add, hsmul_sum, hsmul_smul, ← pow_add, Nat.add_assoc]
  have hmiddle := algebraMiddleHead_signed_cancel.{u, v, w} k A M p q c m
    (PiTensorProduct.tprod k x) (PiTensorProduct.tprod k y)
  exact add_middle_cancel (T := T) _ _ _ _ _ _ hmiddle

/-- The A-balanced deconcatenation chain identity.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, for p+q=n, Dₚ,ᵩ ∘ bₙ = (bₚ,ULift A ⊗ id) ∘ Dₚ₊₁,ᵩ + (-1)ᵖ(id ⊗ bᵩ,M) ∘ Dₚ,ᵩ₊₁, with
both successor cuts in degree n+1. -/
theorem algebraDeconcatCutAt_boundary (p q n : ℕ) (h : p + q = n) :
    (algebraDeconcatCutAt k A M p q n h).comp (algebraBoundary k A M n) =
      (TensorProduct.map (algebraBoundary k A (ULift.{w} A) p) LinearMap.id).comp
        (algebraDeconcatCutAt k A M (p + 1) q (n + 1) (by omega)) +
      (-1 : ℤ) ^ p •
        (TensorProduct.map LinearMap.id (algebraBoundary k A M q)).comp
          (algebraDeconcatCutAt k A M p (q + 1) (n + 1) (by omega)) := by
  subst n
  apply LinearMap.restrictScalars_injective k
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  change algebraDeconcatCutAt k A M p q (p + q) rfl
      (algebraBoundary k A M (p + q) (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    TensorProduct.map (algebraBoundary k A (ULift.{w} A) p) LinearMap.id
      (algebraDeconcatCutAt k A M (p + 1) q (p + q + 1) (by omega)
        (m ⊗ₜ[k] PiTensorProduct.tprod k a)) +
    (-1 : ℤ) ^ p • TensorProduct.map LinearMap.id (algebraBoundary k A M q)
      (algebraDeconcatCutAt k A M p (q + 1) (p + q + 1) (by omega)
        (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  obtain ⟨x, c, y, ha⟩ := exists_pivotWord p q a
  subst a
  exact algebraDeconcatCutAt_boundary_pivot k A M p q m x c y

end ModuleCat.Algebra.Hochschild.Symmetric
