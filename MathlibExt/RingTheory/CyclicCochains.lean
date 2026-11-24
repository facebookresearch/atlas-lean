/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
/-
Ported from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/RingTheory/CyclicCohomology/Cochain.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Ring.GeomSum
import MathlibExt.Algebra.BigOperators.CyclicAlternatingSum
import MathlibExt.Data.Fin.CyclicCoordinates
import MathlibExt.Data.Fin.CyclicTupleCoordinates

/-!
# The Hochschild coboundary and cyclic cochains

For a possibly nonunital and nonassociative `R`-algebra `A` and an `R`-module `M`, an
`n`-cochain is an `R`-multilinear map `φ : Aⁿ⁺¹ → M`. This file constructs the Hochschild
coboundary
`b : Cⁿ → Cⁿ⁺¹`,
`(bφ)(a₀, …, aₙ₊₁) = ∑_{j ≤ n} (-1)ʲ φ(a₀, …, aⱼaⱼ₊₁, …, aₙ₊₁) + (-1)ⁿ⁺¹ φ(aₙ₊₁a₀, a₁, …, aₙ)`,
proves `b ∘ b = 0` when the multiplication is associative, and shows that `b` preserves the cyclic
cochains, those with
`φ(aₙ, a₀, …, aₙ₋₁) = (-1)ⁿ φ(a₀, …, aₙ)`. For unital `A` and `M = R` these are the data from
which the Hochschild cochain complex of `A` with coefficients in its dual `A*` and Connes' cyclic
subcomplex can be assembled; the cyclic complex and its cohomology are constructed in
`TauCeti.RingTheory.CyclicCohomology.Cohomology`. Pulling cochains back along a linear map
preserves cyclicity, and pulling back along a homomorphism of nonunital algebras commutes with `b`.

The coboundary is the alternating sum of the cofaces `φ ↦ φ ∘ dᵢ`, where `dᵢ` are face maps
on tuples. For unital `A`, these faces and the rotation are part of the Hochschild cyclic module;
in the nonunital setting no degeneracies are provided. The two facts above are consequences of
identities between faces and the cyclic rotation
`t(a₀, …, aₙ₊₁) = (aₙ₊₁, a₀, …, aₙ)`: the simplicial identity
`dᵢ ∘ d_{j+1} = d_j ∘ dᵢ` for `i ≤ j`, and `d₀ ∘ t = d_{n+1}`, `d_{i+1} ∘ t = t ∘ dᵢ`.

## Main definitions

* `TauCeti.hochschildFace`: the faces `dᵢ` on tuples.
* `TauCeti.hochschildCoface`: the cofaces `φ ↦ φ ∘ dᵢ` on multilinear cochains.
* `TauCeti.hochschildCoboundary`: the Hochschild coboundary `b`.
* `TauCeti.cyclicCochains`: the submodule of cyclic cochains.
* `TauCeti.cyclicHochschildCoboundary`: the restriction of `b` to cyclic cochains.
* `TauCeti.cyclicCochainsMap`: the pullback of cyclic cochains along a linear map.

## Main results

* `TauCeti.hochschildCoboundary_hochschildCoboundary`: `b (b φ) = 0`.
* `TauCeti.hochschildCoboundary_mem_cyclicCochains`: `b` maps cyclic cochains to cyclic cochains.
* `TauCeti.hochschildCoboundary_apply_eq_zero_of_add_add_mul_eq_zero`: the Hochschild
  coboundary of a cyclic cochain vanishes on a tuple whose cyclically adjacent entries are
  quasi-inverse.
* `TauCeti.apply_update_const_eq_zero_of_isIdempotentElem`: an even-degree cyclic cocycle vanishes
  on `(e, …, y, …, e)` when `e` is idempotent and `y` is tangent to the idempotents at `e`.
* `TauCeti.cyclicHochschildCoboundary_cyclicHochschildCoboundary`: the restriction of `b` to
  cyclic cochains also squares to zero.
* `TauCeti.hochschildCoboundary_zero_eq_zero_iff`: the degree-zero cocycles are the traces.
* `TauCeti.hochschildCoboundary_compLinearMap`: `b` commutes with pullback along a homomorphism.
* `TauCeti.prod_hochschildFace`: over a commutative monoid the faces preserve the product of the
  entries.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§1.1, 2.1.
-/

public section

open Function

namespace TauCeti

/-! ### Faces on natural-number indexed sequences -/

section NatFace

variable {A : Type*}

/-- Cyclic rotation `(b₀, …, bₙ) ↦ (bₙ, b₀, …, bₙ₋₁)` of a sequence of length `n + 1`. -/
private def natRotate (n : ℕ) (b : ℕ → A) (k : ℕ) : A :=
  if k = 0 then b n else b (k - 1)

private theorem comp_finRotate_symm_comp_val {n : ℕ} (b : ℕ → A) :
    (fun k : Fin (n + 1) ↦ b k) ∘ (finRotate (n + 1)).symm =
      fun k : Fin (n + 1) ↦ natRotate n b k := by
  funext k
  rcases k with ⟨_ | k, hk⟩
  · simp [natRotate, Fin.coe_neg_one]
  · simp [natRotate, finRotate_symm_apply, Fin.val_sub_one_of_ne_zero]

section Mul

variable [Mul A]

/-- Contraction of the entries `i` and `i + 1` of a sequence. -/
private def natContract (i : ℕ) (b : ℕ → A) (k : ℕ) : A :=
  if k < i then b k else if k = i then b k * b (k + 1) else b (k + 1)

private theorem contractNth_comp_val {n : ℕ} (j : Fin (n + 2)) (b : ℕ → A) :
    Fin.contractNth j (· * ·) (fun k : Fin (n + 2) ↦ b k) =
      fun k : Fin (n + 1) ↦ natContract j b k := by
  funext k
  simp only [Fin.contractNth, Fin.val_castSucc, Fin.val_succ, natContract]

end Mul

section Semigroup

variable [Semigroup A]

private theorem natContract_natContract {i j : ℕ} (hij : i ≤ j) (b : ℕ → A) (k : ℕ) :
    natContract i (natContract (j + 1) b) k = natContract j (natContract i b) k := by
  simp only [natContract]
  split_ifs <;> first | omega | simp_all [mul_assoc]

private theorem natContract_natContract_natRotate {n i : ℕ} (hi : i ≤ n) (b : ℕ → A) {k : ℕ}
    (hk : k ≤ n) :
    natContract i (natContract 0 (natRotate (n + 2) b)) k =
      natContract 0 (natRotate (n + 1) (natContract i b)) k := by
  simp only [natContract, natRotate]
  split_ifs <;> first | omega | simp_all [mul_assoc]

private theorem natContract_natRotate_natContract_natRotate {n : ℕ} (b : ℕ → A) {k : ℕ}
    (hk : k ≤ n) :
    natContract 0 (natRotate (n + 1) (natContract 0 (natRotate (n + 2) b))) k =
      natContract 0 (natRotate (n + 1) (natContract (n + 1) b)) k := by
  simp only [natContract, natRotate]
  split_ifs <;> first | omega | simp_all [mul_assoc]

end Semigroup

section Mul

variable [Mul A]

private theorem natContract_succ_natRotate {n i : ℕ} (hi : i < n) (b : ℕ → A) (k : ℕ) :
    natContract (i + 1) (natRotate (n + 1) b) k = natRotate n (natContract i b) k := by
  simp only [natContract, natRotate]
  split_ifs <;> first | omega | simp_all [Nat.sub_one_add_one]

private theorem natContract_natRotate_natRotate {n : ℕ} (b : ℕ → A) {k : ℕ} (hk : k ≤ n) :
    natContract 0 (natRotate (n + 1) (natRotate (n + 1) b)) k =
      natRotate n (natContract n b) k := by
  simp only [natContract, natRotate]
  split_ifs <;> first | omega | simp_all

end Mul

/-- The position of the contracted sequence at which the entry `k` of the original sequence
appears, for the contraction of the entries `j` and `j + 1`. -/
private def natContractPos (j k : ℕ) : ℕ := if k ≤ j then k else k - 1

private theorem natContractPos_lt {n j k : ℕ} (hj : j < n + 1) (hk : k < n + 2) :
    natContractPos j k < n + 1 := by
  simp only [natContractPos]
  split_ifs <;> omega

private theorem natContract_update_of_ne [Mul A] {j k m : ℕ}
    (hm : m ≠ natContractPos j k) (b : ℕ → A) (x : A) :
    natContract j (update b k x) m = natContract j b m := by
  simp only [natContract, natContractPos, update_apply] at hm ⊢
  split_ifs at hm ⊢ <;> first | omega | rfl

/-- Updating one entry of a tuple only changes one entry of a contraction of it. -/
private theorem contractNth_update_comp_val [Mul A] {n : ℕ} (j : Fin (n + 1)) (b : ℕ → A)
    (k : Fin (n + 2)) (x : A) :
    Fin.contractNth j.castSucc (· * ·) (update (fun m : Fin (n + 2) ↦ b m) k x) =
      update (fun m : Fin (n + 1) ↦ natContract j b m)
        ⟨natContractPos j k, natContractPos_lt j.2 k.2⟩
        (natContract j (update b k x) (natContractPos j k)) := by
  have hupd : update (fun m : Fin (n + 2) ↦ b m) k x = fun m : Fin (n + 2) ↦ update b k x m :=
    (update_comp_eq_of_injective b Fin.val_injective k x).symm
  rw [hupd, contractNth_comp_val]
  funext m
  by_cases hm : (m : ℕ) = natContractPos j k
  · obtain rfl : m = ⟨natContractPos j k, natContractPos_lt j.2 k.2⟩ := Fin.ext hm
    rw [update_self, Fin.val_castSucc]
  · rw [update_of_ne (fun h ↦ hm (congrArg Fin.val h)), Fin.val_castSucc,
      natContract_update_of_ne hm]

private theorem natContract_update_add [Distrib A] (j k : ℕ) (b : ℕ → A)
    (x y : A) :
    natContract j (update b k (x + y)) (natContractPos j k) =
      natContract j (update b k x) (natContractPos j k) +
        natContract j (update b k y) (natContractPos j k) := by
  simp only [natContract, natContractPos, update_apply]
  split_ifs <;> first | omega | simp [add_mul, mul_add]

private theorem natContract_update_smul {R : Type*} [Mul A] [SMul R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (j k : ℕ) (b : ℕ → A) (c : R) (x : A) :
    natContract j (update b k (c • x)) (natContractPos j k) =
      c • natContract j (update b k x) (natContractPos j k) := by
  simp only [natContract, natContractPos, update_apply]
  split_ifs <;> first | omega | simp [smul_mul_assoc, mul_smul_comm]

end NatFace

/-! ### Hochschild faces of tuples -/

section Face

variable {A : Type*} {n : ℕ}

section Mul

variable [Mul A]

/-- The `i`-th Hochschild face of a tuple `(a₀, …, aₙ₊₁)`. For `i ≤ n` it multiplies the adjacent
entries `aᵢ` and `aᵢ₊₁`; the last face is `(aₙ₊₁ a₀, a₁, …, aₙ)`, i.e. the zeroth face of the
cyclically rotated tuple `(aₙ₊₁, a₀, …, aₙ)`. -/
def hochschildFace (i : Fin (n + 2)) (a : Fin (n + 2) → A) : Fin (n + 1) → A :=
  Fin.lastCases (Fin.contractNth 0 (· * ·) (a ∘ (finRotate _).symm))
    (fun j ↦ Fin.contractNth j.castSucc (· * ·) a) i

/-- The `j`-th Hochschild face for `j ≤ n` multiplies the entries `j` and `j + 1`. -/
@[simp]
theorem hochschildFace_castSucc (j : Fin (n + 1)) (a : Fin (n + 2) → A) :
    hochschildFace j.castSucc a = Fin.contractNth j.castSucc (· * ·) a := by
  simp [hochschildFace]

/-- The last Hochschild face is the zeroth face of the cyclically rotated tuple. -/
theorem hochschildFace_last_eq_contractNth (a : Fin (n + 2) → A) :
    hochschildFace (Fin.last (n + 1)) a =
      Fin.contractNth 0 (· * ·) (a ∘ (finRotate (n + 2)).symm) := by
  simp [hochschildFace]

/-- The last Hochschild face is `(aₙ₊₁ a₀, a₁, …, aₙ)`. -/
@[simp]
theorem hochschildFace_last (a : Fin (n + 2) → A) :
    hochschildFace (Fin.last (n + 1)) a =
      Fin.cons (a (Fin.last (n + 1)) * a 0) fun k ↦ a k.castSucc.succ := by
  obtain ⟨b, hb⟩ := Fin.val_injective.surjective_comp_right' (fun _ : ℕ ↦ a 0) a
  obtain rfl : a = fun k : Fin _ ↦ b k := hb.symm
  rw [hochschildFace_last_eq_contractNth, comp_finRotate_symm_comp_val, contractNth_comp_val]
  funext k
  cases k using Fin.cases <;> simp [natContract, natRotate]

private theorem hochschildFace_castSucc_comp_val (j : Fin (n + 1)) (b : ℕ → A) :
    hochschildFace j.castSucc (fun k : Fin (n + 2) ↦ b k) =
      fun k : Fin (n + 1) ↦ natContract j b k := by
  rw [hochschildFace_castSucc, contractNth_comp_val, Fin.val_castSucc]

private theorem hochschildFace_last_comp_val (b : ℕ → A) :
    hochschildFace (Fin.last (n + 1)) (fun k : Fin (n + 2) ↦ b k) =
      fun k : Fin (n + 1) ↦ natContract 0 (natRotate (n + 1) b) k := by
  rw [hochschildFace_last_eq_contractNth, comp_finRotate_symm_comp_val, contractNth_comp_val,
    Fin.val_zero]

/-- The zeroth face of the rotated tuple `(aₙ₊₁, a₀, …, aₙ)` is the last face of `a`. -/
theorem hochschildFace_zero_comp_finRotate_symm (a : Fin (n + 2) → A) :
    hochschildFace 0 (a ∘ (finRotate (n + 2)).symm) = hochschildFace (Fin.last (n + 1)) a := by
  rw [← Fin.castSucc_zero, hochschildFace_castSucc, hochschildFace_last_eq_contractNth,
    Fin.castSucc_zero]

/-- The faces commute with cyclic rotation: `d_{i+1} ∘ t = t ∘ dᵢ`. -/
theorem hochschildFace_succ_comp_finRotate_symm (i : Fin (n + 1)) (a : Fin (n + 2) → A) :
    hochschildFace i.succ (a ∘ (finRotate (n + 2)).symm) =
      hochschildFace i.castSucc a ∘ (finRotate (n + 1)).symm := by
  obtain ⟨b, hb⟩ := Fin.val_injective.surjective_comp_right' (fun _ : ℕ ↦ a 0) a
  obtain rfl : a = fun k : Fin _ ↦ b k := hb.symm
  rw [comp_finRotate_symm_comp_val]
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.succ_last, hochschildFace_last_comp_val, hochschildFace_castSucc_comp_val,
      comp_finRotate_symm_comp_val]
    funext k
    exact natContract_natRotate_natRotate b (Nat.le_of_lt_succ k.2)
  | cast i =>
    rw [Fin.succ_castSucc, hochschildFace_castSucc_comp_val, hochschildFace_castSucc_comp_val,
      comp_finRotate_symm_comp_val]
    funext k
    exact natContract_succ_natRotate i.2 b k

/-- A multiplicative map commutes with the Hochschild faces. -/
theorem comp_hochschildFace {B F : Type*} [Mul B] [FunLike F A B] [MulHomClass F A B] (f : F)
    (i : Fin (n + 2)) (a : Fin (n + 2) → A) :
    f ∘ hochschildFace i a = hochschildFace i (f ∘ a) := by
  induction i using Fin.lastCases with
  | last =>
    rw [hochschildFace_last_eq_contractNth, hochschildFace_last_eq_contractNth,
      Fin.comp_contractNth _ _ (map_mul f), Function.comp_assoc]
  | cast j =>
    rw [hochschildFace_castSucc, hochschildFace_castSucc, Fin.comp_contractNth _ _ (map_mul f)]

/-- Every Hochschild face fixes a constant tuple whose entry is idempotent. -/
theorem hochschildFace_const_of_isIdempotentElem {x : A} (hx : IsIdempotentElem x)
    (i : Fin (n + 2)) : hochschildFace i (fun _ ↦ x) = fun _ ↦ x := by
  induction i using Fin.lastCases with
  | last =>
    rw [hochschildFace_last, hx.eq]
    funext k
    cases k using Fin.cases <;> simp
  | cast j =>
    rw [hochschildFace_castSucc]
    funext k
    simp only [Fin.contractNth, hx.eq, ite_self]

end Mul

/-- The two Hochschild faces adjacent to a noninitial unit argument agree. -/
theorem hochschildFace_castSucc_eq_succ_of_apply_succ_eq_one [MulOneClass A]
    (a : Fin (n + 2) → A) (j : Fin (n + 1))
    (ha : a j.succ = 1) : hochschildFace j.castSucc a = hochschildFace j.succ a := by
  have hleft : hochschildFace j.castSucc a = Fin.removeNth j.succ a := by
    simp [hochschildFace_castSucc, Fin.contractNth_castSucc_eq_update_removeNth_succ, ha,
      Fin.removeNth_apply]
  rw [hleft]
  induction j using Fin.lastCases with
  | last =>
    ext k
    cases k using Fin.cases <;> simp_all [Fin.init]
  | cast j =>
    rw [Fin.succ_castSucc] at ha ⊢
    simp only [hochschildFace_castSucc, Fin.contractNth_castSucc_eq_update_removeNth_succ, ha,
      one_mul, Fin.update_removeNth_succ_eq_removeNth_castSucc]

/-- In a commutative monoid every Hochschild face preserves the product of the entries. -/
@[simp]
theorem prod_hochschildFace [CommMonoid A] (i : Fin (n + 2)) (a : Fin (n + 2) → A) :
    ∏ k, hochschildFace i a k = ∏ k, a k := by
  induction i using Fin.lastCases with
  | last =>
    rw [hochschildFace_last_eq_contractNth, ← Fin.castSucc_zero, Fin.prod_contractNth_castSucc]
    exact Equiv.prod_comp (finRotate (n + 2)).symm a
  | cast j => rw [hochschildFace_castSucc, Fin.prod_contractNth_castSucc]

/-- The simplicial identity `dᵢ ∘ d_{j+1} = d_j ∘ dᵢ` for `i ≤ j` between Hochschild faces. -/
theorem hochschildFace_hochschildFace [Semigroup A] {i j : Fin (n + 2)} (hij : i ≤ j)
    (a : Fin (n + 3) → A) :
    hochschildFace i (hochschildFace j.succ a) =
      hochschildFace j (hochschildFace i.castSucc a) := by
  obtain ⟨b, hb⟩ := Fin.val_injective.surjective_comp_right' (fun _ : ℕ ↦ a 0) a
  obtain rfl : a = fun k : Fin _ ↦ b k := hb.symm
  induction j using Fin.lastCases with
  | last =>
    rw [Fin.succ_last, hochschildFace_last_comp_val]
    induction i using Fin.lastCases with
    | last =>
      rw [hochschildFace_last_comp_val, hochschildFace_castSucc_comp_val,
        hochschildFace_last_comp_val]
      funext k
      exact natContract_natRotate_natContract_natRotate b (Nat.le_of_lt_succ k.2)
    | cast i =>
      rw [hochschildFace_castSucc_comp_val, hochschildFace_castSucc_comp_val,
        hochschildFace_last_comp_val]
      funext k
      exact natContract_natContract_natRotate (Nat.le_of_lt_succ i.2) b (Nat.le_of_lt_succ k.2)
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact absurd hij (not_le.2 (Fin.castSucc_lt_last j))
    | cast i =>
      rw [Fin.succ_castSucc, hochschildFace_castSucc_comp_val, hochschildFace_castSucc_comp_val,
        hochschildFace_castSucc_comp_val, hochschildFace_castSucc_comp_val]
      funext k
      exact natContract_natContract (Fin.castSucc_le_castSucc_iff.1 hij) b k

end Face

/-! ### Cochains and the Hochschild coboundary -/

section Cochain

variable (R A M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommMonoid M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

variable {R A M} in
/-- Precomposition of a cochain with the contraction of the entries `j` and `j + 1`. -/
private def contractCoface (j : Fin (n + 1)) (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n +
    1) ↦ A) M) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M where
  toFun a := φ (Fin.contractNth j.castSucc (· * ·) a)
  map_update_add' := by
    intro _ a k x y
    obtain rfl : ‹DecidableEq (Fin (n + 2))› = instDecidableEqFin _ := Subsingleton.elim _ _
    obtain ⟨b, hb⟩ := Fin.val_injective.surjective_comp_right' (fun _ : ℕ ↦ a 0) a
    obtain rfl : a = fun k : Fin _ ↦ b k := hb.symm
    simp only [contractNth_update_comp_val, natContract_update_add, MultilinearMap.map_update_add]
  map_update_smul' := by
    intro _ a k c x
    obtain rfl : ‹DecidableEq (Fin (n + 2))› = instDecidableEqFin _ := Subsingleton.elim _ _
    obtain ⟨b, hb⟩ := Fin.val_injective.surjective_comp_right' (fun _ : ℕ ↦ a 0) a
    obtain rfl : a = fun k : Fin _ ↦ b k := hb.symm
    simp only [contractNth_update_comp_val, natContract_update_smul,
      MultilinearMap.map_update_smul]

omit [SMulCommClass R R M] in
private theorem contractCoface_apply (j : Fin (n + 1))
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) (a : Fin (n + 2) → A) :
    contractCoface j φ a = φ (Fin.contractNth j.castSucc (· * ·) a) :=
  rfl

variable {R A M} in
/-- The multilinear map `a ↦ φ (dᵢ a)`, assembled from contractions and a cyclic reindexing. -/
private def cofaceAux (i : Fin (n + 2)) (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦
    A) M) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M :=
  Fin.lastCases ((contractCoface 0 φ).domDomCongr (finRotate (n + 2)).symm)
    (fun j ↦ contractCoface j φ) i

omit [SMulCommClass R R M] in
private theorem cofaceAux_apply (i : Fin (n + 2))
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) (a : Fin (n + 2) → A) :
    cofaceAux i φ a = φ (hochschildFace i a) := by
  induction i using Fin.lastCases with
  | last =>
    simp only [cofaceAux, Fin.lastCases_last, MultilinearMap.domDomCongr_apply,
      contractCoface_apply, hochschildFace_last_eq_contractNth, Function.comp_def,
      Fin.castSucc_zero]
  | cast j =>
    simp only [cofaceAux, Fin.lastCases_castSucc, contractCoface_apply, hochschildFace_castSucc]

/-- The `i`-th Hochschild coface, sending an `n`-cochain `φ` (a multilinear map in `n + 1`
arguments) to the `(n + 1)`-cochain `a ↦ φ (dᵢ a)`. -/
def hochschildCoface (i : Fin (n + 2)) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M where
  toFun := cofaceAux i
  map_add' φ ψ := by ext a; simp only [cofaceAux_apply, add_apply]
  map_smul' c φ := by ext a; simp only [cofaceAux_apply, smul_apply, RingHom.id_apply]

/-- The `i`-th coface evaluates a cochain on the `i`-th Hochschild face of the tuple. -/
@[simp]
theorem hochschildCoface_apply (i : Fin (n + 2))
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) (a : Fin (n + 2) → A) :
    hochschildCoface R A M i φ a = φ (hochschildFace i a) :=
  cofaceAux_apply R A M i φ a

end Cochain

/-! ### Cyclic cochains -/

section Cyclic

variable (R A M : Type*) [Semiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M]
  [Module R M] [SMulCommClass R R M] {n : ℕ}

/-- The cyclic `n`-cochains: the multilinear maps `φ` in `n + 1` arguments with
`φ(aₙ, a₀, …, aₙ₋₁) = (-1)ⁿ φ(a₀, …, aₙ)`. -/
def cyclicCochains (n : ℕ) : Submodule R (MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A)
    M) where
  carrier := {φ | ∀ a, φ (a ∘ (finRotate (n + 1)).symm) = (-1 : ℤ) ^ n • φ a}
  add_mem' {φ ψ} hφ hψ a := by simp [hφ a, hψ a]
  zero_mem' a := by simp
  smul_mem' c φ hφ a := by simp [hφ a, smul_comm c]

variable {R A M} in
/-- A cochain is cyclic exactly when rotating its arguments multiplies its value by `(-1)ⁿ`. -/
@[simp]
theorem mem_cyclicCochains_iff {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M} :
    φ ∈ cyclicCochains R A M n ↔
      ∀ a : Fin (n + 1) → A, φ (a ∘ (finRotate (n + 1)).symm) = (-1 : ℤ) ^ n • φ a :=
  Iff.rfl

/-- A bundled cyclic cochain satisfies the characteristic cyclic rotation identity. -/
@[simp]
theorem cyclicCochains_apply_finRotate_symm (φ : cyclicCochains R A M n)
    (a : Fin (n + 1) → A) :
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M)
        (a ∘ (finRotate (n + 1)).symm) =
      (-1 : ℤ) ^ n • (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) a :=
  (mem_cyclicCochains_iff.1 φ.property) a

variable {R A M} in
/-- On a constant tuple, a cyclic cochain of odd degree takes a value `v` with `v = -v`. -/
theorem apply_const_eq_neg_of_mem_cyclicCochains
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M
        n)
    (hn : Odd n) (x : A) : φ (fun _ ↦ x) = -φ (fun _ ↦ x) := by
  have h := hφ fun _ ↦ x
  simpa only [Function.comp_def, hn.neg_one_pow, neg_one_smul] using h

variable {R A M} in
/-- In even degree, a cyclic cochain takes the same value when the single distinguished entry of
an otherwise constant tuple moves to the first slot. -/
private theorem apply_update_const_eq_apply_update_const_zero (hn : Even n)
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M
        n)
    (e z : A) (k : Fin (n + 1)) :
    φ (Function.update (fun _ ↦ e) k z) = φ (Function.update (fun _ ↦ e) 0 z) := by
  induction k using Fin.induction with
  | zero => rfl
  | succ k ih =>
    have h := mem_cyclicCochains_iff.1 hφ (Function.update (fun _ ↦ e) k.castSucc z)
    rw [Function.update_comp_equiv, Equiv.symm_symm, hn.neg_one_pow, one_smul] at h
    rw [← ih, ← h]
    congr 2
    exact Fin.ext (by simp)

/-- Every `0`-cochain is cyclic. -/
@[simp]
theorem cyclicCochains_zero : cyclicCochains R A M 0 = ⊤ :=
  eq_top_iff.2 fun φ _ a ↦ by simp [finRotate_one]

variable {R A M} in
/-- A `1`-cochain is cyclic exactly when it is antisymmetric: `φ(a₁, a₀) = -φ(a₀, a₁)`. -/
theorem mem_cyclicCochains_one_iff {φ : MultilinearMap (RingHom.id R) (fun _ : Fin 2 ↦ A) M} :
    φ ∈ cyclicCochains R A M 1 ↔ ∀ x y : A, φ ![y, x] = -φ ![x, y] := by
  have hrot (a : Fin 2 → A) : a ∘ (finRotate 2).symm = ![a 1, a 0] := by
    funext i; fin_cases i <;> rfl
  have heta (a : Fin 2 → A) : a = ![a 0, a 1] := by
    funext i; fin_cases i <;> rfl
  refine ⟨fun hφ x y ↦ ?_, fun hφ a ↦ ?_⟩
  · simpa [hrot] using hφ ![x, y]
  · rw [hrot, hφ, ← heta, pow_one, neg_one_smul]

variable {R A M} in
/-- A `2`-cochain is cyclic exactly when it is invariant under cyclic rotation of its arguments:
`φ(a₂, a₀, a₁) = φ(a₀, a₁, a₂)`. -/
theorem mem_cyclicCochains_two_iff {φ : MultilinearMap (RingHom.id R) (fun _ : Fin 3 ↦ A) M} :
    φ ∈ cyclicCochains R A M 2 ↔ ∀ x y z : A, φ ![z, x, y] = φ ![x, y, z] := by
  have hrot (a : Fin 3 → A) : a ∘ (finRotate 3).symm = ![a 2, a 0, a 1] := by
    funext i; fin_cases i <;> rfl
  have heta (a : Fin 3 → A) : a = ![a 0, a 1, a 2] := by
    funext i; fin_cases i <;> rfl
  refine ⟨fun hφ x y z ↦ ?_, fun hφ a ↦ ?_⟩
  · simpa [hrot] using hφ ![x, y, z]
  · rw [hrot, hφ, ← heta, neg_one_sq, one_smul]

end Cyclic

section QuasiInverse

variable {R A M ι : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [AddCommGroup M] [Module R M] [DecidableEq ι]

/-- A multilinear map evaluated on a product `pq` of quasi-inverse elements, `q + p + pq = 0`, in
one slot is minus the sum of its values on `p` and on `q` in that slot. -/
theorem _root_.MultilinearMap.map_update_mul_of_add_add_mul_eq_zero
    (f : MultilinearMap (RingHom.id R) (fun _ : ι ↦ A) M) (r : ι → A) (j : ι) {p q : A}
    (h : q + p + p * q = 0) :
    f (Function.update r j (p * q)) =
      -(f (Function.update r j p) + f (Function.update r j q)) := by
  have h0 := f.map_update_zero r j
  rw [← h, f.map_update_add, f.map_update_add, add_comm (f _) (f (Function.update r j p))] at h0
  exact eq_neg_of_add_eq_zero_right h0

/-- A multilinear map evaluated on a tuple `x` with the quasi-inverse entries `j` and `j + 1`
multiplied together is minus the sum of its values on `x` with entry `j + 1` or entry `j`
deleted. -/
theorem _root_.MultilinearMap.map_contractNth_castSucc_of_add_add_mul_eq_zero {n : ℕ}
    (f : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) (x : Fin (n + 2) → A) (j : Fin
        (n + 1))
    (h : x j.succ + x j.castSucc + x j.castSucc * x j.succ = 0) :
    f (Fin.contractNth j.castSucc (· * ·) x) =
      -(f (Fin.removeNth j.succ x) + f (Fin.removeNth j.castSucc x)) := by
  rw [Fin.contractNth_castSucc_eq_update_removeNth_succ,
    f.map_update_mul_of_add_add_mul_eq_zero _ _ h, Fin.update_removeNth_succ_eq_removeNth_castSucc,
    Function.update_eq_self_iff.2 (by simp [Fin.removeNth_apply])]

end QuasiInverse

section Coboundary

section NonAssoc

variable (R A M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- The Hochschild coboundary `b` on `M`-valued cochains of `A`, the alternating sum
`∑ᵢ (-1)ⁱ φ ∘ dᵢ` of the cofaces. Explicitly (`hochschildCoboundary_apply_eq_sum_contractNth_add`),
`(bφ)(a₀, …, aₙ₊₁) = ∑_{j ≤ n} (-1)ʲ φ(a₀, …, aⱼaⱼ₊₁, …, aₙ₊₁) + (-1)ⁿ⁺¹ φ(aₙ₊₁a₀, a₁, …, aₙ)`. -/
def hochschildCoboundary (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • hochschildCoface R A M i

variable {R A M} {n : ℕ}

/-- The Hochschild coboundary evaluates as the alternating sum of `φ` on the faces of the tuple. -/
@[simp]
theorem hochschildCoboundary_apply (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 2) → A) :
    hochschildCoboundary R A M n φ a =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (hochschildFace i a) := by
  simp [hochschildCoboundary]

/-- The Hochschild coboundary in the explicit form of the multiplication of adjacent entries,
followed by the cyclic term. -/
theorem hochschildCoboundary_apply_eq_sum_contractNth_add
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) (a : Fin (n + 2) → A) :
    hochschildCoboundary R A M n φ a =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) • φ (Fin.contractNth j.castSucc (· * ·) a) +
        (-1 : ℤ) ^ (n + 1) •
          φ (Fin.cons (a (Fin.last (n + 1)) * a 0) fun k ↦ a k.castSucc.succ) := by
  rw [hochschildCoboundary_apply, Fin.sum_univ_castSucc]
  simp

end NonAssoc

section Assoc

variable (R A M : Type*) [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

/-- The Hochschild coboundary squares to zero. -/
@[simp]
theorem hochschildCoboundary_hochschildCoboundary
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    hochschildCoboundary R A M (n + 1) (hochschildCoboundary R A M n φ) = 0 := by
  ext a
  simp only [hochschildCoboundary_apply, zero_apply]
  exact sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero
    (fun i j ↦ φ (hochschildFace j (hochschildFace i a)))
    fun i j hij ↦ by simp only [hochschildFace_hochschildFace hij]

/-- The Hochschild coboundary squares to zero, as a composite of linear maps. -/
theorem hochschildCoboundary_comp_hochschildCoboundary :
    hochschildCoboundary R A M (n + 1) ∘ₗ hochschildCoboundary R A M n = 0 :=
  LinearMap.ext fun φ ↦ hochschildCoboundary_hochschildCoboundary (R := R) (A := A) (M := M) φ

end Assoc

section NonAssoc

variable (R A M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

/-- In degree zero, `(bφ)(a₀, a₁) = φ(a₀a₁) - φ(a₁a₀)`. -/
theorem hochschildCoboundary_zero_apply (φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ A) M)
    (a : Fin 2 → A) :
    hochschildCoboundary R A M 0 φ a = φ (fun _ ↦ a 0 * a 1) - φ (fun _ ↦ a 1 * a 0) := by
  have h₀ : Fin.contractNth (0 : Fin 1).castSucc (· * ·) a = fun _ ↦ a 0 * a 1 := by
    funext k
    fin_cases k
    rfl
  have h₁ : (Fin.cons (a (Fin.last 1) * a 0) fun k : Fin 0 ↦ a k.castSucc.succ : Fin 1 → A) =
      fun _ ↦ a 1 * a 0 := by
    funext k
    fin_cases k
    rfl
  rw [hochschildCoboundary_apply_eq_sum_contractNth_add, Fin.sum_univ_one, h₀, h₁]
  simp [sub_eq_add_neg]

/-- In degree one, `(bφ)(a₀, a₁, a₂) = φ(a₀a₁, a₂) - φ(a₀, a₁a₂) + φ(a₂a₀, a₁)`. -/
theorem hochschildCoboundary_one_apply (φ : MultilinearMap (RingHom.id R) (fun _ : Fin 2 ↦ A) M)
    (a : Fin 3 → A) :
    hochschildCoboundary R A M 1 φ a =
      φ ![a 0 * a 1, a 2] - φ ![a 0, a 1 * a 2] + φ ![a 2 * a 0, a 1] := by
  have h₀ : Fin.contractNth (0 : Fin 2).castSucc (· * ·) a = ![a 0 * a 1, a 2] := by
    funext i; fin_cases i <;> rfl
  have h₁ : Fin.contractNth (1 : Fin 2).castSucc (· * ·) a = ![a 0, a 1 * a 2] := by
    funext i; fin_cases i <;> rfl
  have h₂ : (Fin.cons (a (Fin.last 2) * a 0) fun i : Fin 1 ↦ a i.castSucc.succ : Fin 2 → A) =
      ![a 2 * a 0, a 1] := by
    funext i; fin_cases i <;> rfl
  rw [hochschildCoboundary_apply_eq_sum_contractNth_add, Fin.sum_univ_two, h₀, h₁, h₂]
  simp [sub_eq_add_neg]

/-- In degree two, `(bφ)(a₀, a₁, a₂, a₃)` is
`φ(a₀a₁, a₂, a₃) - φ(a₀, a₁a₂, a₃) + φ(a₀, a₁, a₂a₃) - φ(a₃a₀, a₁, a₂)`. -/
theorem hochschildCoboundary_two_apply (φ : MultilinearMap (RingHom.id R) (fun _ : Fin 3 ↦ A) M)
    (a : Fin 4 → A) :
    hochschildCoboundary R A M 2 φ a =
      φ ![a 0 * a 1, a 2, a 3] - φ ![a 0, a 1 * a 2, a 3] + φ ![a 0, a 1, a 2 * a 3] -
        φ ![a 3 * a 0, a 1, a 2] := by
  have h₀ : Fin.contractNth (0 : Fin 3).castSucc (· * ·) a = ![a 0 * a 1, a 2, a 3] := by
    funext i; fin_cases i <;> rfl
  have h₁ : Fin.contractNth (1 : Fin 3).castSucc (· * ·) a = ![a 0, a 1 * a 2, a 3] := by
    funext i; fin_cases i <;> rfl
  have h₂ : Fin.contractNth (2 : Fin 3).castSucc (· * ·) a = ![a 0, a 1, a 2 * a 3] := by
    funext i; fin_cases i <;> rfl
  have h₃ : (Fin.cons (a (Fin.last 3) * a 0) fun i : Fin 2 ↦ a i.castSucc.succ : Fin 3 → A) =
      ![a 3 * a 0, a 1, a 2] := by
    funext i; fin_cases i <;> rfl
  rw [hochschildCoboundary_apply_eq_sum_contractNth_add, Fin.sum_univ_three, h₀, h₁, h₂, h₃]
  simp [sub_eq_add_neg]

/-- A degree-zero cochain is a Hochschild cocycle exactly when it is a trace. -/
theorem hochschildCoboundary_zero_eq_zero_iff (φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦
    A) M) :
    hochschildCoboundary R A M 0 φ = 0 ↔ ∀ x y : A, φ (fun _ ↦ x * y) = φ (fun _ ↦ y * x) := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ ?_⟩
  · have hxy := DFunLike.congr_fun h ![x, y]
    rw [hochschildCoboundary_zero_apply, zero_apply, sub_eq_zero] at hxy
    simpa using hxy
  · ext a
    rw [hochschildCoboundary_zero_apply, h, sub_self, zero_apply]

variable {R A M} in
/-- All faces fix a constant tuple with idempotent entry, so on such a tuple the Hochschild
coboundary of a degree-`n` cochain vanishes for even `n` and is the cochain itself for odd `n`. -/
theorem hochschildCoboundary_apply_const_of_isIdempotentElem
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) {e : A} (he : IsIdempotentElem
        e) :
    hochschildCoboundary R A M n φ (fun _ ↦ e) = if Even n then 0 else φ (fun _ ↦ e) := by
  simp only [hochschildCoboundary_apply, hochschildFace_const_of_isIdempotentElem he,
    ← Finset.sum_smul]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ (-1 : ℤ) ^ i) (n + 2), neg_one_geom_sum]
  split_ifs <;> simp_all [Nat.even_add_one]

/-- The Hochschild coboundary preserves cyclic cochains. When the multiplication is associative,
so that `b ∘ b = 0`, the cyclic cochains therefore form a subcomplex. -/
theorem hochschildCoboundary_mem_cyclicCochains
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M
        n) :
    hochschildCoboundary R A M n φ ∈ cyclicCochains R A M (n + 1) := by
  rw [mem_cyclicCochains_iff] at hφ ⊢
  intro a
  rw [hochschildCoboundary_apply, hochschildCoboundary_apply, Fin.sum_univ_succ,
    Fin.sum_univ_castSucc (n := n + 1), hochschildFace_zero_comp_finRotate_symm]
  simp only [hochschildFace_succ_comp_finRotate_symm, hφ _, smul_add, Finset.smul_sum, smul_smul,
    ← pow_add, Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last, pow_zero, one_smul]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [add_right_comm, add_comm _ n, add_right_comm]
  · rw [← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

variable {R A M} in
/-- **The Hochschild coboundary of a cyclic cochain vanishes on quasi-inverse chains.** If the
cyclically adjacent entries `xᵢ`, `xᵢ₊₁` (indices modulo `n + 2`) of a tuple satisfy
`xᵢ₊₁ + xᵢ + xᵢxᵢ₊₁ = 0`, then `(bψ)(x₀, …, xₙ₊₁) = 0` for every cyclic `n`-cochain `ψ`. -/
theorem hochschildCoboundary_apply_eq_zero_of_add_add_mul_eq_zero
    {ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M} (hψ : ψ ∈ cyclicCochains R A M
        n)
    {x : Fin (n + 2) → A}
    (hx : ∀ i, x (finRotate (n + 2) i) + x i + x i * x (finRotate (n + 2) i) = 0) :
    hochschildCoboundary R A M n ψ x = 0 := by
  -- With `g i = (-1)ⁱ ψ(x with entry i deleted)`, the inner faces contribute `g (j + 1) - g j`.
  set g : Fin (n + 2) → M := fun i ↦ (-1 : ℤ) ^ (i : ℕ) • ψ (Fin.removeNth i x) with hg
  have hinner (j : Fin (n + 1)) : (-1 : ℤ) ^ (j : ℕ) • ψ (Fin.contractNth j.castSucc (· * ·) x) =
      g j.succ - g j.castSucc := by
    have hj := hx j.castSucc
    rw [Fin.finRotate_castSucc] at hj
    rw [ψ.map_contractNth_castSucc_of_add_add_mul_eq_zero _ _ hj]
    simp only [hg, Fin.val_succ, Fin.val_castSucc, pow_succ, mul_neg_one, neg_smul, smul_neg,
      smul_add]
    abel
  -- The last face contributes `g 0 - g (n + 1)`, by cyclicity of `ψ`.
  have hlast : (-1 : ℤ) ^ (n + 1) •
      ψ (Fin.cons (x (Fin.last (n + 1)) * x 0) fun k ↦ x k.castSucc.succ) =
        g 0 - g (Fin.last (n + 1)) := by
    have hl := hx (Fin.last (n + 1))
    rw [finRotate_last] at hl
    -- By definition, the inner entries `fun k ↦ x k.castSucc.succ` are `Fin.init (Fin.tail x)`
    -- and `x (Fin.last (n + 1))` is `Fin.tail x (Fin.last n)`.
    have hinit : (Fin.cons (x 0) fun k ↦ x k.castSucc.succ : Fin (n + 1) → A) = Fin.init x := by
      rw [← Fin.cons_self_tail (Fin.init x), Fin.tail_init_eq_init_tail]
      rfl
    have htail : (Fin.cons (x (Fin.last (n + 1))) fun k ↦ x k.castSucc.succ : Fin (n + 1) → A) =
        Fin.tail x ∘ (finRotate (n + 1)).symm := by
      rw [← Fin.snoc_init_self (Fin.tail x), Fin.snoc_eq_cons_rotate]
      funext k
      rw [Function.comp_apply, Equiv.apply_symm_apply]
      rfl
    rw [← Fin.update_cons_zero (x (Fin.last (n + 1))),
      ψ.map_update_mul_of_add_add_mul_eq_zero _ _ hl, Fin.update_cons_zero, Fin.update_cons_zero,
      hinit, htail, mem_cyclicCochains_iff.1 hψ]
    have hsign : (-1 : ℤ) ^ (n + 1) * (-1) ^ n = -1 := by
      rw [← pow_add]
      exact Odd.neg_one_pow ⟨n, by omega⟩
    simp only [hg, Fin.val_zero, Fin.val_last, Fin.removeNth_zero, Fin.removeNth_last, pow_zero,
      one_smul, smul_neg, smul_add, smul_smul, hsign, neg_one_smul]
    abel
  rw [hochschildCoboundary_apply_eq_sum_contractNth_add, Finset.sum_congr rfl fun j _ ↦ hinner j,
    Finset.sum_sub_distrib, hlast]
  have hsucc := Fin.sum_univ_succ g
  rw [Fin.sum_univ_castSucc] at hsucc
  rw [sub_add_sub_comm, ← sub_eq_zero_of_eq hsucc.symm]
  abel

/-- The Hochschild coboundary `b` restricted to the submodules of cyclic cochains, as a linear
map `C_λⁿ → C_λⁿ⁺¹`. It squares to zero when the multiplication is associative. -/
def cyclicHochschildCoboundary (n : ℕ) :
    cyclicCochains R A M n →ₗ[R] cyclicCochains R A M (n + 1) :=
  (hochschildCoboundary R A M n).restrict fun _ ↦ hochschildCoboundary_mem_cyclicCochains R A M

/-- The restricted coboundary agrees with `b` on underlying cochains. -/
@[simp]
theorem coe_cyclicHochschildCoboundary_apply (φ : cyclicCochains R A M n) :
    (cyclicHochschildCoboundary R A M n φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A)
        M) =
      hochschildCoboundary R A M n φ := by
  simp [cyclicHochschildCoboundary]

end NonAssoc

section Assoc

variable (R A M : Type*) [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

/-- The restricted coboundary on cyclic cochains squares to zero. -/
@[simp]
theorem cyclicHochschildCoboundary_cyclicHochschildCoboundary (φ : cyclicCochains R A M n) :
    cyclicHochschildCoboundary R A M (n + 1) (cyclicHochschildCoboundary R A M n φ) = 0 := by
  ext a
  simp

/-- The restricted coboundary on cyclic cochains squares to zero, as a composite of linear
maps. -/
theorem cyclicHochschildCoboundary_comp_cyclicHochschildCoboundary :
    cyclicHochschildCoboundary R A M (n + 1) ∘ₗ cyclicHochschildCoboundary R A M n = 0 :=
  LinearMap.ext fun φ ↦
    cyclicHochschildCoboundary_cyclicHochschildCoboundary (R := R) (A := A) (M := M) φ

end Assoc

section Idempotent

variable {R A M : Type*} [Semiring R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M] [SMulCommClass R R M]

/-- **Infinitesimal invariance of the even pairing.** Let `φ` be a cyclic cocycle of even degree
and `e` an idempotent. If `y` is tangent to the idempotents at `e`, that is `e y + y e = y`, then
`φ` vanishes on the tuple `(e, …, e)` with one entry replaced by `y`. -/
theorem apply_update_const_eq_zero_of_isIdempotentElem {n : ℕ} (hn : Even n)
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M
        n)
    (hbφ : hochschildCoboundary R A M n φ = 0) {e y : A} (he : IsIdempotentElem e)
    (hy : e * y + y * e = y) (k : Fin (n + 1)) :
    φ (Function.update (fun _ ↦ e) k y) = 0 := by
  rw [apply_update_const_eq_apply_update_const_zero hn hφ]
  -- Tangency forces `e y e = 0`, so `y = x e - e x` for `x = y e - e y`.
  have hey : e * (y * e) = 0 := by
    have h : e * (y * e) + e * (y * e) = e * (y * e) := by
      conv_rhs => rw [← hy]
      simp only [mul_add, add_mul, mul_assoc, he.eq, he.mul_self_mul]
    simpa using h
  set x := y * e - e * y
  have hxy : x * e - e * x = y := by
    simp only [x, sub_mul, mul_sub, mul_assoc, he.eq, he.mul_self_mul, hey, sub_zero, zero_sub,
      sub_neg_eq_add]
    rwa [add_comm]
  -- Evaluate `bφ = 0` on `(x, e, …, e)`: the middle faces cancel in even degree.
  have hb := congrArg (fun ψ ↦ ψ (Fin.cons x fun _ ↦ e)) hbφ
  simp only [hochschildCoboundary_apply_eq_sum_contractNth_add, Fin.sum_univ_succ] at hb
  have h0 : Fin.contractNth (0 : Fin (n + 1)).castSucc (· * ·)
      (Fin.cons x fun _ ↦ e : Fin (n + 2) → A) = Function.update (fun _ ↦ e) 0 (x * e) := by
    funext k
    cases k using Fin.cases <;> simp [Fin.contractNth]
  have hj (j : Fin n) : Fin.contractNth j.succ.castSucc (· * ·)
      (Fin.cons x fun _ ↦ e : Fin (n + 2) → A) = Function.update (fun _ ↦ e) 0 x := by
    funext k
    cases k using Fin.cases <;> simp [Fin.contractNth, he.eq]
  have hl : (Fin.cons ((Fin.cons x fun _ ↦ e : Fin (n + 2) → A) (Fin.last (n + 1)) *
      (Fin.cons x fun _ ↦ e : Fin (n + 2) → A) 0)
      fun k : Fin n ↦ (Fin.cons x fun _ ↦ e : Fin (n + 2) → A) k.castSucc.succ) =
      Function.update (fun _ ↦ e) 0 (e * x) := by
    funext k
    cases k using Fin.cases <;> simp
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, h0, hj, hl, zero_apply] at hb
  rw [← Finset.sum_smul, Fin.sum_univ_eq_sum_range (fun i ↦ (-1 : ℤ) ^ (i + 1)) n] at hb
  simp only [pow_succ, mul_neg_one, Finset.sum_neg_distrib, neg_one_geom_sum, hn, ↓reduceIte,
    neg_zero, zero_smul, add_zero, (hn.add_one).neg_one_pow, neg_one_smul] at hb
  rwa [← hxy, φ.map_update_sub, sub_eq_add_neg]

end Idempotent

end Coboundary

/-! ### Pullback of cochains -/

section Pullback

variable {R A B C M : Type*} [Semiring R] [AddCommGroup M] [Module R M] [SMulCommClass R R M]
  {n : ℕ}

section Linear

variable [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B] [AddCommMonoid C]
  [Module R C]

/-- Pulling a cyclic cochain back along a linear map gives a cyclic cochain. -/
theorem compLinearMap_mem_cyclicCochains (f : A →ₗ[R] B)
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M} (hφ : φ ∈ cyclicCochains R B M
        n) :
    (φ.compLinearMap fun _ ↦ f) ∈ cyclicCochains R A M n :=
  fun a ↦ hφ (f ∘ a)

variable (M) in
/-- The pullback `φ ↦ φ ∘ (f × ⋯ × f)` of cyclic cochains along a linear map. This is built
directly rather than from `MultilinearMap.compLinearMapₗ`, which needs `R` to be commutative. -/
def cyclicCochainsMap (f : A →ₗ[R] B) (n : ℕ) :
    cyclicCochains R B M n →ₗ[R] cyclicCochains R A M n where
  toFun φ := ⟨(φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M).compLinearMap fun _ ↦
      f,
    compLinearMap_mem_cyclicCochains f φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The pullback of a cyclic cochain evaluates the cochain on the images of the arguments. -/
@[simp]
theorem coe_cyclicCochainsMap_apply (f : A →ₗ[R] B) (φ : cyclicCochains R B M n) :
    (cyclicCochainsMap M f n φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) =
      (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M).compLinearMap fun _ ↦ f :=
  (rfl)

variable (M) in
/-- Pulling back along the identity is the identity. -/
@[simp]
theorem cyclicCochainsMap_id (n : ℕ) :
    cyclicCochainsMap M (LinearMap.id : A →ₗ[R] A) n = LinearMap.id := by
  ext φ a
  simp

variable (M) in
/-- Pulling back along a composite is the composite of the pullbacks, in the opposite order. -/
theorem cyclicCochainsMap_comp (f : A →ₗ[R] B) (g : B →ₗ[R] C) (n : ℕ) :
    cyclicCochainsMap M (g ∘ₗ f) n = cyclicCochainsMap M f n ∘ₗ cyclicCochainsMap M g n := by
  ext φ a
  simp

end Linear

section Algebra

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalNonAssocSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]

/-- The Hochschild coboundary commutes with pulling cochains back along a homomorphism of
nonunital algebras. -/
theorem hochschildCoboundary_compLinearMap (f : A →ₙₐ[R] B)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M) :
    hochschildCoboundary R A M n (φ.compLinearMap fun _ ↦ (f : A →ₗ[R] B)) =
      (hochschildCoboundary R B M n φ).compLinearMap fun _ ↦ (f : A →ₗ[R] B) := by
  ext a
  simp only [hochschildCoboundary_apply, MultilinearMap.compLinearMap_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 2
  exact comp_hochschildFace f i a

/-- Pulling cyclic cochains back along a homomorphism of nonunital algebras commutes with the
Hochschild coboundary. -/
theorem cyclicHochschildCoboundary_cyclicCochainsMap (f : A →ₙₐ[R] B)
    (φ : cyclicCochains R B M n) :
    cyclicHochschildCoboundary R A M n (cyclicCochainsMap M (f : A →ₗ[R] B) n φ) =
      cyclicCochainsMap M (f : A →ₗ[R] B) (n + 1) (cyclicHochschildCoboundary R B M n φ) := by
  ext : 1
  simp [hochschildCoboundary_compLinearMap]

end Algebra

end Pullback

end TauCeti
