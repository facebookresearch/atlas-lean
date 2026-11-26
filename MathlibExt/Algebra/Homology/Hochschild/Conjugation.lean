/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.TensorPower.Insert
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitalComparison
public import MathlibExt.Algebra.Homology.Hochschild.Maps
public import MathlibExt.AlgebraicTopology.SemiSimplicialObject.Homotopy
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Unit conjugation is homotopic to the Hochschild identity

Let `k` be a commutative ring, `A` a unital `k`-algebra, and `M` a bimodule with commuting
left and right actions compatible with `k`. For a unit `c ∈ Aˣ`, put `α(a) = c⁻¹ac` and `γ(m)
= c⁻¹ • (m • c)`. Acting by `γ` on the coefficient and `α` on each tail factor defines a
Hochschild chain map.

For `0 ≤ i ≤ n`, the insertion map `h_i` sends a coefficient-first word to the word with
coefficient `m • c`, conjugated first `i` tail factors, inserted element `c⁻¹`, and unchanged
remaining tail. The face identities give a semisimplicial homotopy from conjugation to the
identity and a chain homotopy with degree-`n` component `-∑ᵢ (-1)^i h_i`. Thus conjugation
induces the identity in every degree where homology is defined. The scalar, algebra, and
coefficient universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators
open scoped Simplicial

namespace ModuleCat.Algebra.Hochschild.Conjugation

universe u v w

variable (k : Type u) [CommRing k]
  {A : Type v} [Ring A] [Algebra k A]

/-- The inverse-unit conjugation algebra homomorphism.

For `c ∈ Aˣ`, the `k`-algebra map sends `a` to `c⁻¹ac`. -/
def algebraMap (c : Aˣ) : A →ₐ[k] A :=
  MulSemiringAction.toAlgHom k A (ConjAct.toConjAct (c⁻¹))

/-- The value of inverse-unit algebra conjugation.

For `a ∈ A`, conjugation has value `c.inv * a * c.val`, with this multiplication order. -/
@[simp]
theorem algebraMap_apply (c : Aˣ) (a : A) :
    algebraMap k c a = c.inv * a * c.val := rfl

variable {M : Type w} [AddCommGroup M] [Module k M]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- The coefficient map given by right multiplication by a unit.

For a bimodule coefficient `m`, this ground-linear map has value `op(c.val) • m`, representing
`m • c`. -/
def rightCoefficient (c : Aˣ) : M →ₗ[k] M :=
  Algebra.lsmul k k M (A := Aᵐᵒᵖ) (MulOpposite.op c.val)

/-- The bimodule coefficient conjugation map.

For `c ∈ Aˣ`, first act on the right by `c`, then on the left by `c⁻¹`, giving `m ↦ c⁻¹ •
(op(c) • m)`. -/
def coefficientMap (c : Aˣ) : M →ₗ[k] M :=
  (Algebra.lsmul k k M (A := A) c.inv).comp (rightCoefficient k c)
omit [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M] [Module A M] in
/-- The right-unit coefficient value.

Right coefficient multiplication sends `m` to `op(c.val) • m`. -/
@[simp]
theorem rightCoefficient_apply (c : Aˣ) (m : M) :
    rightCoefficient k c m = MulOpposite.op c.val • m := rfl
omit [SMulCommClass A Aᵐᵒᵖ M] in
/-- The value of bimodule coefficient conjugation.

The coefficient conjugation map sends `m` to `c.inv • (op(c.val) • m)`. -/
@[simp]
theorem coefficientMap_apply (c : Aˣ) (m : M) :
    coefficientMap k c m = c.inv • (MulOpposite.op c.val • m) := rfl

/-- Compatibility of coefficient conjugation with the left action.

For `a ∈ A`, one has `γ(a • m) = α(a) • γ(m)`, where `α(a) = c⁻¹ac` and `γ(m) = c⁻¹ • (m •
c)`. -/
theorem coefficientMap_left (c : Aˣ) (a : A) (m : M) :
    coefficientMap k c (a • m) = algebraMap k c a • coefficientMap k c m := by
  change c.inv • (MulOpposite.op c.val • (a • m)) =
    (c.inv * a * c.val) • (c.inv • (MulOpposite.op c.val • m))
  calc
    _ = c.inv • (a • (MulOpposite.op c.val • m)) :=
      congrArg (fun x : M => c.inv • x) (smul_comm a (MulOpposite.op c.val) m).symm
    _ = (c.inv * a) • (MulOpposite.op c.val • m) := (mul_smul _ _ _).symm
    _ = ((c.inv * a * c.val) * c.inv) • (MulOpposite.op c.val • m) := by
      rw [mul_assoc, mul_assoc, c.val_inv, mul_one]
    _ = _ := mul_smul _ _ _

/-- Compatibility of coefficient conjugation with the right action.

For `a ∈ A`, one has `γ(op(a) • m) = op(α(a)) • γ(m)`, with the opposite-ring action encoding
right multiplication. -/
theorem coefficientMap_right (c : Aˣ) (a : A) (m : M) :
    coefficientMap k c (MulOpposite.op a • m) =
      MulOpposite.op (algebraMap k c a) • coefficientMap k c m := by
  change c.inv • (MulOpposite.op c.val • (MulOpposite.op a • m)) =
    MulOpposite.op (c.inv * a * c.val) •
      (c.inv • (MulOpposite.op c.val • m))
  have hc : c.val * (c.inv * a * c.val) = a * c.val := by
    rw [← mul_assoc c.val (c.inv * a) c.val,
      ← mul_assoc c.val c.inv a, c.val_inv, one_mul]
  calc
    _ = c.inv • ((MulOpposite.op c.val * MulOpposite.op a) • m) :=
      congrArg (fun x : M => c.inv • x) (mul_smul _ _ _).symm
    _ = c.inv •
        ((MulOpposite.op (c.inv * a * c.val) * MulOpposite.op c.val) • m) := by
      rw [← MulOpposite.op_mul, ← MulOpposite.op_mul]
      exact congrArg (fun x : A => c.inv • (MulOpposite.op x • m)) hc.symm
    _ = c.inv •
        (MulOpposite.op (c.inv * a * c.val) • (MulOpposite.op c.val • m)) :=
      congrArg (fun x : M => c.inv • x) (mul_smul _ _ _)
    _ = _ := smul_comm c.inv (MulOpposite.op (c.inv * a * c.val)) _

/-- The degreewise Hochschild conjugation map.

In degree `n`, act on the coefficient by `γ` and on each algebra tensor factor by `α(a) =
c⁻¹ac`. -/
def degreeMap (c : Aˣ) (n : ℕ) :
    M ⊗[k] TensorPower k n A →ₗ[k] M ⊗[k] TensorPower k n A :=
  ModuleCat.Algebra.Hochschild.linearMap
    (algebraMap k c).toNonUnitalAlgHom (coefficientMap k c) n
omit [SMulCommClass A Aᵐᵒᵖ M] in
/-- The tensor formula for Hochschild conjugation.

The degree-`n` map sends `m ⊗ ⊗ᵢ aᵢ` to `γ(m) ⊗ ⊗ᵢ α(aᵢ)`. -/
@[simp]
theorem degreeMap_tprod (c : Aˣ) (n : ℕ) (m : M) (a : Fin n → A) :
    degreeMap k c n (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      coefficientMap k c m ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j => algebraMap k c (a j)) := by
  rw [degreeMap, ModuleCat.Algebra.Hochschild.linearMap_tprod]
  rfl

/-- The conjugation map before an insertion cut.

For a cut `i` and tail index `j`, use the algebra conjugation map if `j < i` and the identity
linear map otherwise. -/
def prefixMap (c : Aˣ) {n : ℕ} (i : Fin (n + 1)) (j : Fin n) : A →ₗ[k] A :=
  if j.val < i.val then (algebraMap k c).toLinearMap else LinearMap.id

/-- The algebra word of a conjugation insertion.

Insert `c⁻¹` at position `i`, conjugate the preceding `i` tail factors, and retain the
remaining tail factors in their order. -/
def word (c : Aˣ) {n : ℕ} (i : Fin (n + 1)) (a : Fin n → A) :
    Fin (n + 1) → A :=
  Fin.insertNth i c.inv (fun j => prefixMap k c i j (a j))

/-- The coefficient-first insertion in the conjugation homotopy.

In degree `n` and at cut `i`, multiply the coefficient on the right by `c`, conjugate the
first `i` tail factors, insert `c⁻¹`, and retain the remaining tail. -/
def hi (c : Aˣ) (n : ℕ) (i : Fin (n + 1)) :
    M ⊗[k] TensorPower k n A →ₗ[k] M ⊗[k] TensorPower k (n + 1) A :=
  TensorProduct.map (rightCoefficient k c)
    ((TensorPower.insert k i c.inv).comp
      (PiTensorProduct.map fun j => prefixMap k c i j))
omit [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M] [Module A M] in
/-- The tensor formula for a conjugation insertion.

The insertion sends `m ⊗ ⊗ⱼ aⱼ` to `(op(c.val) • m) ⊗` the word obtained by conjugating the
prefix, inserting `c⁻¹`, and retaining the tail. -/
@[simp]
theorem hi_tprod (c : Aˣ) (n : ℕ) (i : Fin (n + 1)) (m : M) (a : Fin n → A) :
    hi k c n i (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      rightCoefficient k c m ⊗ₜ[k] PiTensorProduct.tprod k (word k c i a) := by
  simp only [hi, TensorProduct.map_tmul, LinearMap.comp_apply,
    PiTensorProduct.map_tprod, TensorPower.insert_tprod, word]

/-- The inserted value in a conjugation word.

At the insertion position `i`, the word has value `c⁻¹`. -/
@[simp]
theorem word_insert (c : Aˣ) {n : ℕ} (i : Fin (n + 1)) (a : Fin n → A) :
    word k c i a i = c.inv :=
  Fin.insertNth_apply_same _ _ _

/-- The surviving values in a conjugation word.

At the position corresponding to a surviving input index `j`, the word has value `c⁻¹aⱼc` when
`j<i`, and `aⱼ` otherwise. -/
theorem word_succAbove (c : Aˣ) {n : ℕ} (i : Fin (n + 1))
    (a : Fin n → A) (j : Fin n) :
    word k c i a (i.succAbove j) =
      if j.val < i.val then algebraMap k c (a j) else a j := by
  rw [word, Fin.insertNth_apply_succAbove]
  unfold prefixMap
  split <;> rfl


/-- The conjugation word at the first insertion cut.

At cut zero, the output word is `c⁻¹` followed by the unchanged input tail. -/
@[simp]
theorem word_zero (c : Aˣ) (n : ℕ) (a : Fin n → A) :
    word k c (0 : Fin (n + 1)) a = Fin.cons c.inv a := by
  unfold word
  have hp : (fun j : Fin n => prefixMap k c (0 : Fin (n + 1)) j (a j)) = a := by
    funext j
    simp only [prefixMap, Fin.val_zero, Nat.not_lt_zero, ite_false, LinearMap.id_apply]
  rw [hp, Fin.insertNth_zero']

/-- The conjugation word at the last insertion cut.

At the final cut, the output word is the fully conjugated input tail followed by `c⁻¹`. -/
@[simp]
theorem word_last (c : Aˣ) (n : ℕ) (a : Fin n → A) :
    word k c (Fin.last n) a = Fin.snoc (fun j => algebraMap k c (a j)) c.inv := by
  unfold word
  have hp : (fun j : Fin n => prefixMap k c (Fin.last n) j (a j)) =
      (fun j => algebraMap k c (a j)) := by
    funext j
    simp only [prefixMap, Fin.val_last, j.is_lt, ite_true]
    rfl
  rw [hp, Fin.insertNth_last']

/-- The Hochschild chain map of unit conjugation.

Conjugating the coefficient by `γ` and every tail factor by `α` gives an endomorphism of the
Hochschild chain complex. -/
def chainMap (c : Aˣ) :
    ModuleCat.Algebra.Hochschild.chainComplex k A M ⟶
      ModuleCat.Algebra.Hochschild.chainComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (degreeMap k c n)) (by
    intro n
    rw [ModuleCat.Algebra.Hochschild.chainComplex_d]
    apply ModuleCat.hom_ext
    change (ModuleCat.Algebra.Hochschild.boundary k A M n).hom.comp
        (degreeMap (M := M) k c (n + 1)) =
      (degreeMap (M := M) k c n).comp
        (ModuleCat.Algebra.Hochschild.boundary k A M n).hom
    exact ModuleCat.Algebra.Hochschild.linearMap_boundary_comm
      (algebraMap k c).toNonUnitalAlgHom (coefficientMap k c)
      (coefficientMap_left k c) (coefficientMap_right k c) n)

/-- The components of the Hochschild conjugation chain map.

The degree-`n` component is the module map induced by the tensor conjugation map in that
degree. -/
@[simp]
theorem chainMap_f (c : Aˣ) (n : ℕ) :
    ((chainMap (M := M) k c).f n).hom = degreeMap (M := M) k c n := rfl

/-- The identity endpoint of conjugation insertion.

In degree `n`, the first face after the first insertion satisfies `d₀ h₀ = id` on coefficient-
first Hochschild tensors. -/
theorem hi_zero_face (c : Aˣ) (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.face k A M n 0).hom.comp (hi k c n 0) =
      (LinearMap.id : M ⊗[k] TensorPower k n A →ₗ[k] M ⊗[k] TensorPower k n A) := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  change (ModuleCat.Algebra.Hochschild.face k A M n 0).hom
      (hi k c n 0 (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    m ⊗ₜ[k] PiTensorProduct.tprod k a
  rw [hi_tprod, word_zero, ModuleCat.Algebra.Hochschild.face_first_tprod]
  have hm : MulOpposite.op c.inv • rightCoefficient k c m = m := by
    rw [rightCoefficient_apply, ← mul_smul, ← MulOpposite.op_mul,
      c.val_inv, MulOpposite.op_one, one_smul]
  simp only [Fin.cons_zero]
  rw [hm]
  congr 1

/-- The conjugation endpoint of the last insertion.

In degree `n`, the last face after the last insertion satisfies `d_(n+1) h_n = γ_n`, where
`γ_n` is the degreewise coefficient-and-algebra conjugation map. -/
theorem hi_last_face (c : Aˣ) (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.face k A M n (Fin.last (n + 1))).hom.comp
        (hi k c n (Fin.last n)) = degreeMap k c n := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  change (ModuleCat.Algebra.Hochschild.face k A M n (Fin.last (n + 1))).hom
      (hi k c n (Fin.last n) (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    degreeMap k c n (m ⊗ₜ[k] PiTensorProduct.tprod k a)
  rw [hi_tprod, word_last, ModuleCat.Algebra.Hochschild.face_last_tprod, degreeMap_tprod]
  simp only [Fin.snoc_last, coefficientMap_apply, rightCoefficient_apply]
  congr 1
  apply congrArg (PiTensorProduct.tprod k)
  funext j
  simp only [ModuleCat.Algebra.Hochschild.hochschildDropLast, Fin.snoc_castSucc]


/- Generic tuple identities adapted from the MatrixMoritaFaces proof
by @toskua. They retain the native Fin insertion maps and add no carrier. -/
private theorem mul_insert_succ {D : Type*} [Mul D] {n : ℕ}
    (i : Fin (n + 1)) (c : D) (a : Fin (n + 1) → D) :
    ModuleCat.Algebra.Hochschild.hochschildMulAdjacent i
        (Fin.insertNth (α := fun _ => D) i.succ c a) =
      Function.update a i (a i * c) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, ite_true]
    rw [← Fin.succAbove_succ_self i, Fin.insertNth_apply_succAbove,
      Fin.insertNth_apply_same]
    simp only [Function.update_self]
  · simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, if_neg hj,
      Fin.insertNth_apply_succAbove]
    simp [hj]

private theorem mul_insert_castSucc {D : Type*} [Mul D] {n : ℕ}
    (i : Fin (n + 1)) (c : D) (a : Fin (n + 1) → D) :
    ModuleCat.Algebra.Hochschild.hochschildMulAdjacent i
        (Fin.insertNth (α := fun _ => D) i.castSucc c a) =
      Function.update a i (c * a i) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, ite_true]
    rw [Fin.insertNth_apply_same, ← Fin.succAbove_castSucc_self i,
      Fin.insertNth_apply_succAbove]
    simp only [Function.update_self]
  · have hs : i.succ.succAbove j = i.castSucc.succAbove j := by
      by_cases hlt : j < i
      · rw [Fin.succAbove_succ_of_le _ _ hlt.le, Fin.succAbove_castSucc_of_lt _ _ hlt]
      · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hj)
        rw [Fin.succAbove_succ_of_lt _ _ hij, Fin.succAbove_castSucc_of_le _ _ hij.le]
    simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, if_neg hj, hs,
      Fin.insertNth_apply_succAbove]
    simp [hj]

private theorem mul_insert_before {D : Type*} [Mul D] {n : ℕ}
    (p : Fin n) (j : Fin (n + 1)) (h : p.val < j.val)
    (c : D) (a : Fin (n + 1) → D) :
    ModuleCat.Algebra.Hochschild.hochschildMulAdjacent p.castSucc
        (Fin.insertNth (α := fun _ => D) j.succ c a) =
      Fin.insertNth (α := fun _ => D) j c
        (ModuleCat.Algebra.Hochschild.hochschildMulAdjacent p a) := by
  have hpj : p.succ ≤ j := Fin.le_iff_val_le_val.mpr (Nat.succ_le_of_lt h)
  have hpmap : j.succAbove p = p.castSucc :=
    Fin.succAbove_of_castSucc_lt j p (Fin.lt_def.mpr h)
  have hcomm (l : Fin n) :
      p.castSucc.succ.succAbove (j.succAbove l) =
        j.succ.succAbove (p.succ.succAbove l) := by
    simpa only [Fin.succ_succAbove_succ, hpmap, Fin.succ_castSucc,
      Fin.predAbove_succ_of_le p.succ j hpj] using
      Fin.succAbove_succAbove_succAbove_predAbove j.succ p.succ l
  refine Fin.eq_insertNth_iff.mpr ⟨?_, ?_⟩
  · have hjp : j ≠ p.castSucc := Fin.ne_of_gt (Fin.lt_def.mpr h)
    simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, if_neg hjp,
      Fin.succAbove_succ_of_lt p.castSucc j (Fin.lt_def.mpr h),
      Fin.insertNth_apply_same]
  · funext l
    change ModuleCat.Algebra.Hochschild.hochschildMulAdjacent p.castSucc
      (Fin.insertNth (α := fun _ => D) j.succ c a) (j.succAbove l) =
      ModuleCat.Algebra.Hochschild.hochschildMulAdjacent p a l
    by_cases hl : l = p
    · subst l
      simp only [hpmap, ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, ite_true]
      have hlo : j.succ.succAbove p.castSucc = p.castSucc.castSucc :=
        Fin.succAbove_succ_of_le j p.castSucc
          (Fin.le_iff_val_le_val.mpr h.le)
      have hhi : j.succ.succAbove p.succ = p.castSucc.succ := by
        simpa only [Fin.succ_castSucc] using Fin.succAbove_succ_of_le j p.succ hpj
      rw [← hlo, Fin.insertNth_apply_succAbove, ← hhi, Fin.insertNth_apply_succAbove]
    · have hn : j.succAbove l ≠ p.castSucc := by
        intro he
        apply hl
        apply Fin.succAbove_right_injective
        exact he.trans hpmap.symm
      simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, if_neg hl,
        if_neg hn, hcomm, Fin.insertNth_apply_succAbove]

private theorem mul_insert_after {D : Type*} [Mul D] {n : ℕ}
    (p : Fin n) (j : Fin (n + 1)) (h : j.val ≤ p.val)
    (c : D) (a : Fin (n + 1) → D) :
    ModuleCat.Algebra.Hochschild.hochschildMulAdjacent p.succ
        (Fin.insertNth (α := fun _ => D) j.castSucc c a) =
      Fin.insertNth (α := fun _ => D) j c
        (ModuleCat.Algebra.Hochschild.hochschildMulAdjacent p a) := by
  have hjp : j ≤ p.castSucc := Fin.le_iff_val_le_val.mpr h
  have hpmap : j.succAbove p = p.succ := Fin.succAbove_of_le_castSucc j p hjp
  have hcomm (l : Fin n) :
      p.succ.succ.succAbove (j.succAbove l) =
        j.castSucc.succAbove (p.succ.succAbove l) := by
    have hpj : p.succ.predAbove j.castSucc = j :=
      Fin.predAbove_castSucc_of_le p.succ j
        (Fin.le_iff_val_le_val.mpr (Nat.le_trans h (Nat.le_succ _)))
    have hskip : j.castSucc.succAbove p.succ = p.succ.succ :=
      Fin.succAbove_castSucc_of_le j p.succ
        (Fin.le_iff_val_le_val.mpr (Nat.le_trans h (Nat.le_succ _)))
    simpa only [hpj, hskip] using
      Fin.succAbove_succAbove_succAbove_predAbove j.castSucc p.succ l
  refine Fin.eq_insertNth_iff.mpr ⟨?_, ?_⟩
  · have hjn : j ≠ p.succ := Fin.ne_of_lt
      (Fin.lt_def.mpr (Nat.lt_succ_of_le h))
    simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, if_neg hjn,
      Fin.succAbove_succ_of_le p.succ j
        (Fin.le_iff_val_le_val.mpr (Nat.le_trans h (Nat.le_succ _))),
      Fin.insertNth_apply_same]
  · funext l
    change ModuleCat.Algebra.Hochschild.hochschildMulAdjacent p.succ
      (Fin.insertNth (α := fun _ => D) j.castSucc c a) (j.succAbove l) =
      ModuleCat.Algebra.Hochschild.hochschildMulAdjacent p a l
    by_cases hl : l = p
    · subst l
      simp only [hpmap, ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, ite_true]
      have hlo : j.castSucc.succAbove p.castSucc = p.succ.castSucc := by
        simpa only [Fin.succ_castSucc] using
          Fin.succAbove_castSucc_of_le j p.castSucc hjp
      have hhi : j.castSucc.succAbove p.succ = p.succ.succ :=
        Fin.succAbove_castSucc_of_le j p.succ
          (Fin.le_iff_val_le_val.mpr (Nat.le_trans h (Nat.le_succ _)))
      rw [← hlo, Fin.insertNth_apply_succAbove, ← hhi, Fin.insertNth_apply_succAbove]
    · have hn : j.succAbove l ≠ p.succ := by
        intro he
        apply hl
        apply Fin.succAbove_right_injective
        exact he.trans hpmap.symm
      simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, if_neg hl,
        if_neg hn, hcomm, Fin.insertNth_apply_succAbove]

private theorem update_cut {D : Type*} {n : ℕ} (j : Fin (n + 1))
    (F G : Fin (n + 1) → D) (x : D) :
    Function.update (fun t => if t.val < j.val + 1 then F t else G t) j x =
      Function.update (fun t => if t.val < j.val then F t else G t) j x := by
  funext t
  by_cases ht : t = j
  · subst t
    simp only [Function.update_self]
  · have hv : t.val ≠ j.val := fun h => ht (Fin.ext h)
    have hc : (t.val < j.val + 1) ↔ (t.val < j.val) := by omega
    simp only [Function.update_of_ne ht]
    change (if t.val < j.val + 1 then F t else G t) =
      (if t.val < j.val then F t else G t)
    simp only [hc]

private theorem dropLast_insert {D : Type*} {n : ℕ} (j : Fin (n + 1))
    (c : D) (v : Fin (n + 1) → D) :
    ModuleCat.Algebra.Hochschild.hochschildDropLast
        (Fin.insertNth (α := fun _ => D) j.castSucc c v) =
      Fin.insertNth (α := fun _ => D) j c (ModuleCat.Algebra.Hochschild.hochschildDropLast v) := by
  funext l
  change Fin.insertNth (α := fun _ => D) j.castSucc c v l.castSucc =
    Fin.insertNth (α := fun _ => D) j c (fun t : Fin n => v t.castSucc) l
  refine j.succAboveCases ?_ (fun t => ?_) l
  · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
  · rw [← Fin.castSucc_succAbove_castSucc, Fin.insertNth_apply_succAbove,
      Fin.insertNth_apply_succAbove]

private theorem insert_castSucc_last {D : Type*} {n : ℕ} (j : Fin (n + 1))
    (c : D) (v : Fin (n + 1) → D) :
    Fin.insertNth (α := fun _ => D) j.castSucc c v (Fin.last (n + 1)) = v (Fin.last n) := by
  have he : j.castSucc.succAbove (Fin.last n) = Fin.last (n + 1) := by
    simpa only [Fin.succ_last] using
      Fin.succAbove_castSucc_of_le j (Fin.last n) j.le_last
  rw [← he, Fin.insertNth_apply_succAbove]


private theorem word_eq (c : Aˣ) {n : ℕ} (i : Fin (n + 1)) (a : Fin n → A) :
    word k c i a =
      Fin.insertNth i c.inv
        (fun j => if j.val < i.val then algebraMap k c (a j) else a j) := by
  unfold word
  apply congrArg (fun b : Fin n → A => Fin.insertNth (α := fun _ => A) i c.inv b)
  funext j
  unfold prefixMap
  split <;> rfl

private theorem word_succ (c : Aˣ) {n : ℕ} (j : Fin (n + 1))
    (a : Fin (n + 1) → A) :
    word k c j.succ a =
      Fin.cons (algebraMap k c (a 0))
        (word k c j (ModuleCat.Algebra.Hochschild.hochschildDropFirst a)) := by
  rw [word_eq, word_eq]
  have hp :
      (fun t : Fin (n + 1) =>
        if t.val < j.succ.val then algebraMap k c (a t) else a t) =
      Fin.cons (algebraMap k c (a 0))
        (fun t : Fin n =>
          if t.val < j.val then algebraMap k c (a t.succ) else a t.succ) := by
    funext t
    refine Fin.cases ?_ (fun q => ?_) t
    · simp only [Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, ite_true,
        Fin.cons_zero]
    · simp only [Fin.val_succ, Nat.add_lt_add_iff_right, Fin.cons_succ]
  rw [hp, Fin.insertNth_succ_cons]
  rfl

private theorem word_mul_before (c : Aˣ) {n : ℕ}
    (p : Fin n) (j : Fin (n + 1)) (h : p.val < j.val)
    (a : Fin (n + 1) → A) :
    ModuleCat.Algebra.Hochschild.hochschildMulAdjacent p.castSucc (word k c j.succ a) =
      word k c j (ModuleCat.Algebra.Hochschild.hochschildMulAdjacent p a) := by
  rw [word_eq, word_eq]
  simp only [Fin.val_succ]
  rw [mul_insert_before p j h]
  apply congrArg (fun b : Fin n → A => Fin.insertNth (α := fun _ => A) j c.inv b)
  funext t
  by_cases ht : t = p
  · subst t
    simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, ite_true,
      Fin.val_castSucc, Fin.val_succ, if_pos (Nat.lt_succ_of_lt h),
      if_pos (Nat.add_lt_add_right h 1), if_pos h]
    exact ((algebraMap k c).map_mul _ _).symm
  · simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, if_neg ht]
    have hc : ((p.succ.succAbove t).val < j.val + 1) ↔ (t.val < j.val) := by
      by_cases hle : t ≤ p
      · rw [Fin.succAbove_succ_of_le p t hle]
        have htj : t.val < j.val :=
          lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hle) h
        exact ⟨fun _ => htj, fun _ => Nat.lt_succ_of_lt htj⟩
      · rw [Fin.succAbove_succ_of_lt p t (lt_of_not_ge hle)]
        simp only [Fin.val_succ, Nat.add_lt_add_iff_right]
    simp only [hc]

private theorem word_mul_after (c : Aˣ) {n : ℕ}
    (p : Fin n) (j : Fin (n + 1)) (h : j.val ≤ p.val)
    (a : Fin (n + 1) → A) :
    ModuleCat.Algebra.Hochschild.hochschildMulAdjacent p.succ (word k c j.castSucc a) =
      word k c j (ModuleCat.Algebra.Hochschild.hochschildMulAdjacent p a) := by
  rw [word_eq, word_eq]
  simp only [Fin.val_castSucc]
  rw [mul_insert_after p j h]
  apply congrArg (fun b : Fin n → A => Fin.insertNth (α := fun _ => A) j c.inv b)
  funext t
  by_cases ht : t = p
  · subst t
    simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, ite_true,
      Fin.val_castSucc, Fin.val_succ, if_neg (not_lt_of_ge h),
      if_neg (not_lt_of_ge (Nat.le_trans h (Nat.le_succ _)))]
  · simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, if_neg ht]
    have hc : ((p.succ.succAbove t).val < j.val) ↔ (t.val < j.val) := by
      by_cases hle : t ≤ p
      · rw [Fin.succAbove_succ_of_le p t hle]
        rfl
      · have hpt : p < t := lt_of_not_ge hle
        rw [Fin.succAbove_succ_of_lt p t hpt]
        have hptv : p.val < t.val := Fin.lt_def.mp hpt
        simp only [Fin.val_succ]
        omega
    simp only [hc]

private theorem word_mul_middle (c : Aˣ) {n : ℕ} (j : Fin (n + 1))
    (a : Fin (n + 1) → A) :
    ModuleCat.Algebra.Hochschild.hochschildMulAdjacent j (word k c j.succ a) =
      ModuleCat.Algebra.Hochschild.hochschildMulAdjacent j (word k c j.castSucc a) := by
  rw [word_eq, word_eq, mul_insert_succ, mul_insert_castSucc]
  simp only [Fin.val_succ, Fin.val_castSucc,
    Nat.lt_succ_self, ite_true, lt_self_iff_false, ite_false]
  have hc : algebraMap k c (a j) * c.inv = c.inv * a j := by
    rw [algebraMap_apply, mul_assoc, c.val_inv, mul_one]
  rw [hc]
  exact update_cut j (fun t => algebraMap k c (a t)) a (c.inv * a j)

private theorem word_dropLast (c : Aˣ) {n : ℕ} (j : Fin (n + 1))
    (a : Fin (n + 1) → A) :
    ModuleCat.Algebra.Hochschild.hochschildDropLast (word k c j.castSucc a) =
      word k c j (ModuleCat.Algebra.Hochschild.hochschildDropLast a) := by
  rw [word_eq, dropLast_insert, word_eq]
  apply congrArg (fun b : Fin n → A => Fin.insertNth (α := fun _ => A) j c.inv b)
  funext t
  simp only [ModuleCat.Algebra.Hochschild.hochschildDropLast, Fin.val_castSucc]

private theorem word_castSucc_last (c : Aˣ) {n : ℕ} (j : Fin (n + 1))
    (a : Fin (n + 1) → A) :
    word k c j.castSucc a (Fin.last (n + 1)) = a (Fin.last n) := by
  rw [word_eq, insert_castSucc_last]
  simp only [Fin.val_last, Fin.val_castSucc, if_neg (not_lt_of_ge (Nat.le_of_lt_succ j.isLt))]
omit [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M] [Module A M] in
private theorem rightCoefficient_face (c : Aˣ) (a : A) (m : M) :
    MulOpposite.op (algebraMap k c a) • rightCoefficient k c m =
      rightCoefficient k c (MulOpposite.op a • m) := by
  rw [rightCoefficient_apply, rightCoefficient_apply]
  have hc : c.val * algebraMap k c a = a * c.val := by
    rw [algebraMap_apply, ← mul_assoc c.val (c.inv * a) c.val,
      ← mul_assoc c.val c.inv a, c.val_inv, one_mul]
  calc
    _ = (MulOpposite.op (algebraMap k c a) * MulOpposite.op c.val) • m :=
      (mul_smul _ _ _).symm
    _ = MulOpposite.op (a * c.val) • m := by rw [← MulOpposite.op_mul, hc]
    _ = _ := by rw [MulOpposite.op_mul, mul_smul]

/-- The face identity before a conjugation insertion.

For `i ≤ j`, the insertion family satisfies `d_i h_(j+1) = h_j d_i`, with the degree-dependent
face and insertion indices as stated. -/
theorem hi_face_before (c : Aˣ) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    (ModuleCat.Algebra.Hochschild.face k A M (n + 1) i.castSucc).hom.comp
        (hi k c (n + 1) j.succ) =
      (hi k c n j).comp (ModuleCat.Algebra.Hochschild.face k A M n i).hom := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.comp_apply]
  revert hij
  refine Fin.cases ?_ (fun q => ?_) i
  · intro _
    simp only [Fin.castSucc_zero]
    rw [hi_tprod, word_succ, ModuleCat.Algebra.Hochschild.face_first_tprod,
      ModuleCat.Algebra.Hochschild.face_first_tprod, hi_tprod]
    simp only [Fin.cons_zero]
    rw [rightCoefficient_face]
    congr 1
  · intro hq
    have hqv : q.val < j.val := by
      have hv := Fin.le_iff_val_le_val.mp hq
      simp only [Fin.val_succ, Fin.val_castSucc] at hv
      omega
    have hqn : q.val < n := lt_of_lt_of_le hqv (Nat.le_of_lt_succ j.isLt)
    let p : Fin n := ⟨q.val, hqn⟩
    have hp : p.castSucc = q := Fin.ext rfl
    have hi : q.succ.castSucc = p.castSucc.castSucc.succ := by
      rw [← hp]
      exact Fin.ext rfl
    have hs : q.succ = p.castSucc.succ := by rw [hp]
    rw [hi, hi_tprod, ModuleCat.Algebra.Hochschild.face_inner_tprod,
      hs, ModuleCat.Algebra.Hochschild.face_inner_tprod, hi_tprod,
      word_mul_before k c p j hqv]

/-- The matching faces at adjacent conjugation insertion cuts.

The insertion family satisfies `d_(j+1) h_(j+1) = d_(j+1) h_j`. -/
theorem hi_face_middle (c : Aˣ) {n : ℕ} (j : Fin (n + 1)) :
    (ModuleCat.Algebra.Hochschild.face k A M (n + 1) j.castSucc.succ).hom.comp
        (hi k c (n + 1) j.succ) =
      (ModuleCat.Algebra.Hochschild.face k A M (n + 1) j.castSucc.succ).hom.comp
        (hi k c (n + 1) j.castSucc) := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.comp_apply]
  rw [hi_tprod, hi_tprod, ModuleCat.Algebra.Hochschild.face_inner_tprod,
    ModuleCat.Algebra.Hochschild.face_inner_tprod, word_mul_middle]

/-- The face identity after a conjugation insertion.

For `j<i`, the insertion family satisfies `d_(i+1) h_j = h_j d_i`, including the cyclic final
face. -/
theorem hi_face_after (c : Aˣ) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    (ModuleCat.Algebra.Hochschild.face k A M (n + 1) i.succ).hom.comp
        (hi k c (n + 1) j.castSucc) =
      (hi k c n j).comp (ModuleCat.Algebra.Hochschild.face k A M n i).hom := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.comp_apply]
  revert hji
  refine Fin.lastCases ?_ (fun q => ?_) i
  · intro _
    rw [hi_tprod]
    simp only [Fin.succ_last]
    rw [ModuleCat.Algebra.Hochschild.face_last_tprod, word_castSucc_last,
      ModuleCat.Algebra.Hochschild.face_last_tprod, hi_tprod, word_dropLast,
      rightCoefficient_apply, rightCoefficient_apply]
    rw [smul_comm]
  · intro hq
    have hqv : j.val < q.val := by
      have hv := Fin.lt_def.mp hq
      simp only [Fin.val_castSucc] at hv
      exact hv
    have hq0 : 0 < q.val := lt_of_le_of_lt (Nat.zero_le _) hqv
    let p : Fin n := ⟨q.val - 1, by have hqn := q.isLt; omega⟩
    have hp : p.succ = q := Fin.ext (by dsimp [p]; omega)
    have hs : q.castSucc = p.castSucc.succ := by rw [← hp, Fin.succ_castSucc]
    rw [hi_tprod, ModuleCat.Algebra.Hochschild.face_inner_tprod,
      hs, ModuleCat.Algebra.Hochschild.face_inner_tprod, hi_tprod, ← hp,
      word_mul_after k c p j (by dsimp [p]; omega)]



/-- The conjugation map of the coefficient semisimplicial bar.

The degreewise coefficient-and-algebra conjugation maps commute with every bar face and define
a semisimplicial endomorphism. -/
def barMap (c : Aˣ) :
    let l := (Algebra.lsmul k k M (A := A)).toNonUnitalAlgHom
    let r := (Algebra.lsmul k k M (A := Aᵐᵒᵖ)).toNonUnitalAlgHom
    let X := ModuleCat.Algebra.Hochschild.NonUnital.bar l r
      (fun a b m => smul_comm a b m)
    X ⟶ X := by
  dsimp only
  let l := (Algebra.lsmul k k M (A := A)).toNonUnitalAlgHom
  let r := (Algebra.lsmul k k M (A := Aᵐᵒᵖ)).toNonUnitalAlgHom
  let h := fun (a : A) (b : Aᵐᵒᵖ) (m : M) => smul_comm a b m
  let X := ModuleCat.Algebra.Hochschild.NonUnital.bar l r h
  exact SemiSimplicialObject.homMk (X := X) (Y := X)
    (fun n => ModuleCat.ofHom (degreeMap k c n)) (by
      intro n i
      change ModuleCat.Algebra.Hochschild.NonUnital.face l r h n i ≫
          ModuleCat.ofHom (degreeMap k c n) =
        ModuleCat.ofHom (degreeMap k c (n + 1)) ≫
          ModuleCat.Algebra.Hochschild.NonUnital.face l r h n i
      rw [ModuleCat.Algebra.Hochschild.NonUnital.face_eq_unital]
      apply ModuleCat.hom_ext
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, degreeMap] using
        (ModuleCat.Algebra.Hochschild.linearMap_face_comm
          (algebraMap k c).toNonUnitalAlgHom (coefficientMap k c)
          (coefficientMap_left k c) (coefficientMap_right k c) n i).symm)

/-- The components of coefficient-bar conjugation.

In semisimplicial degree `n`, the conjugation map is the categorical module map associated to
degree-`n` Hochschild tensor conjugation. -/
@[simp]
theorem barMap_app (c : Aˣ) (n : ℕ) :
    (barMap (M := M) k c).app (Opposite.op ⦋n⦌ₛ) =
      ModuleCat.ofHom (degreeMap (M := M) k c n) := rfl

/-- The semisimplicial homotopy from conjugation to the identity.

The insertion maps `h_i` satisfy the two endpoint and three face identities, giving a
semisimplicial homotopy between coefficient-bar conjugation and its identity. -/
def faceHomotopy (c : Aˣ) :
    SemiSimplicialObject.Homotopy (barMap (M := M) k c) (𝟙 _) := by
  let l := (Algebra.lsmul k k M (A := A)).toNonUnitalAlgHom
  let r := (Algebra.lsmul k k M (A := Aᵐᵒᵖ)).toNonUnitalAlgHom
  let h := fun (a : A) (b : Aᵐᵒᵖ) (m : M) => smul_comm a b m
  refine
    { h := fun {n} i => ModuleCat.ofHom (hi k c n i)
      h_zero_comp_δ_zero := ?_
      h_last_comp_δ_last := ?_
      h_succ_comp_δ_castSucc_of_lt := ?_
      h_succ_comp_δ_castSucc_succ := ?_
      h_castSucc_comp_δ_succ_of_lt := ?_ }
  · intro n
    change ModuleCat.ofHom (hi k c n 0) ≫
      ModuleCat.Algebra.Hochschild.NonUnital.face l r h n 0 = 𝟙 _
    rw [ModuleCat.Algebra.Hochschild.NonUnital.face_eq_unital]
    apply ModuleCat.hom_ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id] using
      hi_zero_face k c n
  · intro n
    change ModuleCat.ofHom (hi k c n (Fin.last n)) ≫
      ModuleCat.Algebra.Hochschild.NonUnital.face l r h n (Fin.last (n + 1)) =
        (barMap k c).app (Opposite.op ⦋n⦌ₛ)
    rw [ModuleCat.Algebra.Hochschild.NonUnital.face_eq_unital, barMap_app]
    apply ModuleCat.hom_ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using hi_last_face k c n
  · intro n i j hij
    change ModuleCat.ofHom (hi k c (n + 1) j.succ) ≫
        ModuleCat.Algebra.Hochschild.NonUnital.face l r h (n + 1) i.castSucc =
      ModuleCat.Algebra.Hochschild.NonUnital.face l r h n i ≫
        ModuleCat.ofHom (hi k c n j)
    rw [ModuleCat.Algebra.Hochschild.NonUnital.face_eq_unital,
      ModuleCat.Algebra.Hochschild.NonUnital.face_eq_unital]
    apply ModuleCat.hom_ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      hi_face_before k c i j hij
  · intro n j
    change ModuleCat.ofHom (hi k c (n + 1) j.succ) ≫
        ModuleCat.Algebra.Hochschild.NonUnital.face l r h (n + 1) j.castSucc.succ =
      ModuleCat.ofHom (hi k c (n + 1) j.castSucc) ≫
        ModuleCat.Algebra.Hochschild.NonUnital.face l r h (n + 1) j.castSucc.succ
    rw [ModuleCat.Algebra.Hochschild.NonUnital.face_eq_unital]
    apply ModuleCat.hom_ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using hi_face_middle k c j
  · intro n i j hji
    change ModuleCat.ofHom (hi k c (n + 1) j.castSucc) ≫
        ModuleCat.Algebra.Hochschild.NonUnital.face l r h (n + 1) i.succ =
      ModuleCat.Algebra.Hochschild.NonUnital.face l r h n i ≫
        ModuleCat.ofHom (hi k c n j)
    rw [ModuleCat.Algebra.Hochschild.NonUnital.face_eq_unital,
      ModuleCat.Algebra.Hochschild.NonUnital.face_eq_unital]
    apply ModuleCat.hom_ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      hi_face_after k c i j hji

/-- The chain homotopy from Hochschild conjugation to the identity.

The coefficient-bar insertion homotopy gives a homotopy of the corresponding Hochschild chain
maps, retaining the coefficient-first tensor presentation. -/
def chainHomotopy (c : Aˣ) :
    _root_.Homotopy (chainMap k c) (𝟙 (ModuleCat.Algebra.Hochschild.chainComplex k A M)) := by
  let l : A →ₙₐ[k] Module.End k M :=
    (Algebra.lsmul k k M (A := A)).toNonUnitalAlgHom
  let r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M :=
    (Algebra.lsmul k k M (A := Aᵐᵒᵖ)).toNonUnitalAlgHom
  have h : ∀ (a : A) (b : Aᵐᵒᵖ) (m : M), l a (r b m) = r b (l a m) := by
    intro a b m
    change a • (b • m) = b • (a • m)
    exact smul_comm a b m
  let X : SemiSimplicialObject (ModuleCat.{max u v w} k) :=
    ModuleCat.Algebra.Hochschild.NonUnital.bar l r h
  let K : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
    ModuleCat.Algebra.Hochschild.NonUnital.complex l r h
  let O : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
    ModuleCat.Algebra.Hochschild.chainComplex k A M
  let e : K ≅ O := ModuleCat.Algebra.Hochschild.NonUnital.complexIsoUnital
    (k := k) (A := A) (M := M)
  let T : SemiSimplicialObject (ModuleCat.{max u v w} k) ⥤
      ChainComplex (ModuleCat.{max u v w} k) ℕ :=
    AlgebraicTopology.semiSimplicialAlternatingFaceMapComplex (ModuleCat.{max u v w} k)
  let f : X ⟶ X := barMap (M := M) k c
  let F : K ⟶ K := T.map f
  let H := ((faceHomotopy (M := M) k c).toChainHomotopy.compLeft e.inv).compRight e.hom
  have hf : (e.inv ≫ F) ≫ e.hom = chainMap k c := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    have hc :
        (𝟙 (ModuleCat.Algebra.Hochschild.chainLevel k A M n) ≫
          ModuleCat.ofHom (degreeMap (M := M) k c n)) ≫
            𝟙 (ModuleCat.Algebra.Hochschild.chainLevel k A M n) =
          ModuleCat.ofHom (degreeMap (M := M) k c n) :=
      (congrArg (fun g : ModuleCat.Algebra.Hochschild.chainLevel k A M n ⟶
          ModuleCat.Algebra.Hochschild.chainLevel k A M n =>
            g ≫ 𝟙 (ModuleCat.Algebra.Hochschild.chainLevel k A M n))
        (CategoryTheory.Category.id_comp (ModuleCat.ofHom (degreeMap (M := M) k c n)))).trans
          (CategoryTheory.Category.comp_id (ModuleCat.ofHom (degreeMap (M := M) k c n)))
    have hlin := congrArg
      (fun g : ModuleCat.Algebra.Hochschild.chainLevel k A M n ⟶
          ModuleCat.Algebra.Hochschild.chainLevel k A M n => g.hom) hc
    simp only [e, F, T, f, O, HomologicalComplex.comp_f,
      ModuleCat.Algebra.Hochschild.NonUnital.complexIsoUnital_inv_f,
      ModuleCat.Algebra.Hochschild.NonUnital.complexIsoUnital_hom_f,
      AlgebraicTopology.semiSimplicialAlternatingFaceMapComplex_map_f, barMap_app]
    dsimp only [ModuleCat.Algebra.Hochschild.NonUnital.complex,
      AlgebraicTopology.semiSimplicialAlternatingFaceMapComplex,
      AlgebraicTopology.SemiSimplicialAlternatingFaceMapComplex.obj,
      ModuleCat.Algebra.Hochschild.NonUnital.bar,
      ModuleCat.Algebra.Hochschild.chainComplex, ChainComplex.of,
      chainMap, ChainComplex.ofHom]
    exact hlin
  have hid : T.map (𝟙 X) = 𝟙 K := CategoryTheory.Functor.map_id T X
  have hg : (e.inv ≫ T.map (𝟙 X)) ≫ e.hom = 𝟙 O :=
    (congrArg (fun g : K ⟶ K => (e.inv ≫ g) ≫ e.hom) hid).trans
      ((congrArg (fun g : O ⟶ K => g ≫ e.hom)
        (CategoryTheory.Category.comp_id e.inv)).trans e.inv_hom_id)
  exact (_root_.Homotopy.ofEq hf.symm).trans
    (H.trans (_root_.Homotopy.ofEq hg))

/-- The signed component formula for the conjugation chain homotopy.

In degree `n`, the homotopy component to degree `n+1` is the negative alternating sum
`-∑_(i=0)^n (-1)^i h_i`, with signs acting by integer scalar multiplication. -/
theorem chainHomotopy_hom (c : Aˣ) (n : ℕ) :
    ((chainHomotopy (M := M) k c).hom n (n + 1)).hom =
      -∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • hi (M := M) k c n i := by
  simp only [chainHomotopy, _root_.Homotopy.trans_hom, _root_.Homotopy.ofEq_hom,
    Pi.zero_apply, _root_.Homotopy.compRight_hom, _root_.Homotopy.compLeft_hom,
    ModuleCat.Algebra.Hochschild.NonUnital.complexIsoUnital_inv_f,
    ModuleCat.Algebra.Hochschild.NonUnital.complexIsoUnital_hom_f,
    zero_add, add_zero, SemiSimplicialObject.Homotopy.toChainHomotopy_hom]
  dsimp only [faceHomotopy]
  dsimp only [ModuleCat.Algebra.Hochschild.NonUnital.complex,
    AlgebraicTopology.semiSimplicialAlternatingFaceMapComplex,
    AlgebraicTopology.SemiSimplicialAlternatingFaceMapComplex.obj,
    ModuleCat.Algebra.Hochschild.NonUnital.bar,
    ModuleCat.Algebra.Hochschild.chainComplex, ChainComplex.of]
  dsimp only [ModuleCat.Algebra.Hochschild.NonUnital.chainLevel,
    ModuleCat.Algebra.Hochschild.chainLevel]
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.id_comp, LinearMap.comp_id,
    ModuleCat.hom_neg, ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom]
  rfl

/-- The identity action of unit conjugation on Hochschild homology.

For every degree `n` in which the Hochschild complex has homology, the map induced by
simultaneous algebra and bimodule coefficient conjugation is the identity. -/
theorem homologyMap_eq_id (c : Aˣ) (n : ℕ)
    [(ModuleCat.Algebra.Hochschild.chainComplex k A M).HasHomology n] :
    HomologicalComplex.homologyMap (chainMap (M := M) k c) n = 𝟙 _ := by
  exact (_root_.Homotopy.homologyMap_eq (chainHomotopy (M := M) k c) n).trans
    (HomologicalComplex.homologyMap_id _ n)


end ModuleCat.Algebra.Hochschild.Conjugation
