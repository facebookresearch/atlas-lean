/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.MazurAdmissible
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

@[expose] public section

open MazurAdmissible

/-- Consumer with the original binders: an admissible chain for a prime
`q` in a finite additive commutative group has ambient cardinality
`q ^ filtLength`. -/
example {M : Type*} [AddCommGroup M] {q : ℕ} (hq : q.Prime) {Φ : OpenAction M}
    (c : AdmissibleChain q Φ) : Nat.card M = q ^ filtLength c :=
  c.natCard_eq_pow_filtLength hq

/-- Higher-universe consumer: the same statement in `Type 1`. -/
example {M : Type 1} [AddCommGroup M] {q : ℕ} (hq : q.Prime)
    {Φ : OpenAction M} (c : AdmissibleChain q Φ) :
    Nat.card M = q ^ filtLength c :=
  c.natCard_eq_pow_filtLength hq

/-- `filtLength` is the indexed length `n` of the chain. -/
example {M : Type*} [AddCommGroup M] {q : ℕ} {Φ : OpenAction M}
    (c : AdmissibleChain q Φ) : filtLength c = c.n :=
  rfl

/-- The bundled action has Mathlib's `MonoidHom` API: by `map_inv`, `σ⁻¹`
undoes `σ`. -/
example {M : Type*} [AddCommGroup M] (Φ : OpenAction M)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M) :
    (Φ.φ σ⁻¹).toAdd ((Φ.φ σ).toAdd x) = x := by
  rw [map_inv, toAdd_inv, AddAut.neg_apply_self]

/-- The unbundled laws are corollaries: the action is compatible with
composition, and the identity acts as the identity. -/
example {M : Type*} [AddCommGroup M] (Φ : OpenAction M)
    (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M) :
    (Φ.φ (σ * τ)).toAdd x = (Φ.φ σ).toAdd ((Φ.φ τ).toAdd x) ∧
      (Φ.φ 1).toAdd x = x := by
  rw [Φ.map_mul, Φ.map_one, AddAut.add_apply, AddAut.zero_apply]
  exact ⟨rfl, rfl⟩

/-- A Galois element lies in the kernel of the bundled action exactly when it
fixes `M` pointwise. -/
example {M : Type*} [AddCommGroup M] (Φ : OpenAction M)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ ∈ Φ.φ.ker ↔ ∀ x, (Φ.φ σ).toAdd x = x := by
  rw [MonoidHom.mem_ker, ← toAdd_eq_zero, AddEquiv.ext_iff]
  simp only [AddAut.zero_apply]

/-- The trivial action is an open action: its kernel is the whole group. -/
private noncomputable def trivialAction (M : Type*) [AddCommGroup M] : OpenAction M where
  φ := 1
  hker := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ

/-- Every step is trivial for the trivial action. -/
private theorem isTrivialStep_trivialAction {M : Type*} [AddCommGroup M] (A B : AddSubgroup M) :
    IsTrivialStep (trivialAction M) A B := by
  intro σ x _
  simp [trivialAction]

/-- Mathlib's `DistribMulAction.toAddAut` has the bundled form, so a
distributive Galois action with open kernel is an open action, acting by
`σ • x`. -/
example {M : Type*} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (h : IsOpen
      ((DistribMulAction.toAddAut (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M).ker :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M) :
    ((⟨DistribMulAction.toAddAut _ M, h⟩ : OpenAction M).φ σ).toAdd x = σ • x :=
  rfl

/-- The one-step chain `⊥ ≤ ⊤` of `ZMod p` has quotient of `Nat.card` `p`, for every `p`. -/
private theorem natCard_top_quotient_bot (p : ℕ) :
    Nat.card (↥(⊤ : AddSubgroup (ZMod p)) ⧸ (⊥ : AddSubgroup (ZMod p)).addSubgroupOf ⊤) = p := by
  rw [AddSubgroup.bot_addSubgroupOf, Nat.card_congr QuotientAddGroup.quotientBot.toEquiv,
    AddSubgroup.card_top, Nat.card_zmod]

/-- The one-step chain `⊥ ≤ ⊤` of `ZMod p` with the trivial action, its step tagged `b`, given
the condition the tag names. -/
private noncomputable def zmodChain (p : ℕ) (b : Bool)
    (h : if b then IsTrivialStep (trivialAction (ZMod p)) ⊥ ⊤
      else IsCyclotomicStep p (trivialAction (ZMod p)) ⊥ ⊤) :
    AdmissibleChain p (trivialAction (ZMod p)) where
  n := 1
  step := ![⊥, ⊤]
  hbot := rfl
  htop := rfl
  hmono i := by fin_cases i; exact bot_le
  tag _ := b
  hcard i := by fin_cases i; exact natCard_top_quotient_bot p
  hact i := by fin_cases i; exact h

/-- `ZMod p` with the trivial action has the one-step chain `⊥ ≤ ⊤` with its step tagged `true`,
and `filtAlpha` counts that step. This holds for every `p`, `p = 0` included. -/
example (p : ℕ) :
    filtLength (zmodChain p true (isTrivialStep_trivialAction ⊥ ⊤)) = 1 ∧
      filtAlpha (zmodChain p true (isTrivialStep_trivialAction ⊥ ⊤)) = 1 :=
  ⟨rfl, rfl⟩

/-- For a prime `p`, `ZMod p` with the trivial action is Mazur admissible at `p`. -/
example {p : ℕ} (hp : p.Prime) : IsMazurAdmissible p (trivialAction (ZMod p)) :=
  ⟨hp, ⟨zmodChain p true (isTrivialStep_trivialAction ⊥ ⊤)⟩⟩

/-- Level zero is rejected. `ZMod 0` is `ℤ`, so the quotient of its one-step chain is infinite and
has `Nat.card` equal to `0`: the chain exists at `p = 0`, but `IsMazurAdmissible` asks for a
prime. -/
example : Nonempty (AdmissibleChain 0 (trivialAction (ZMod 0))) ∧
    ¬ IsMazurAdmissible 0 (trivialAction (ZMod 0)) :=
  ⟨⟨zmodChain 0 true (isTrivialStep_trivialAction ⊥ ⊤)⟩, fun h => Nat.not_prime_zero h.1⟩

/-- A prime alone is not enough: an admissible chain for `2` would make the order of `ZMod 3` a
power of `2`, so `ZMod 3` with the trivial action is not Mazur admissible at `2`. -/
example : ¬ IsMazurAdmissible 2 (trivialAction (ZMod 3)) := by
  rintro ⟨hp, ⟨c⟩⟩
  have h := c.natCard_eq_pow_filtLength hp
  rw [Nat.card_zmod, filtLength_eq] at h
  generalize c.n = k at h
  rcases k with _ | k
  · simp at h
  · rw [pow_succ] at h
    omega

/-- For a prime `p`, each subgroup of an admissible chain is stable under the action, so the
chain is a filtration by Galois submodules. -/
example {M : Type*} [AddCommGroup M] {p : ℕ} (hp : p.Prime) {Φ : OpenAction M}
    (c : AdmissibleChain p Φ) (i : Fin (c.n + 1))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {x : M} (hx : x ∈ c.step i) :
    (Φ.φ σ).toAdd x ∈ c.step i := by
  induction i using Fin.cases with
  | zero =>
    rw [c.hbot, AddSubgroup.mem_bot] at hx
    rw [hx, map_zero]
    exact zero_mem _
  | succ i =>
    have hle := c.hmono i
    have h := c.hact i
    split_ifs at h with htag
    · simpa using add_mem (hle (h σ x hx)) hx
    · have : NeZero p := ⟨hp.ne_zero⟩
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure ℚ) p
      obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ)
        (by rw [← map_pow, hζ.pow_eq_one, map_one])
      simpa using add_mem (hle (h σ ζ hζ a ha.symm x hx)) (nsmul_mem hx a)

/-- For `p = 2` a step of order `2` is trivial exactly when it is cyclotomic: `-1` is the only
primitive square root of unity, and every Galois element fixes it. So for `p = 2` the tags of a
chain, and with them `filtAlpha`, are a free choice. -/
private theorem isTrivialStep_iff_isCyclotomicStep_two {M : Type*} [AddCommGroup M]
    (Φ : OpenAction M) {A B : AddSubgroup M}
    (hcard : Nat.card (↥B ⧸ A.addSubgroupOf B) = 2) :
    IsTrivialStep Φ A B ↔ IsCyclotomicStep 2 Φ A B := by
  have h2 : ∀ x ∈ B, 2 • x ∈ A := by
    intro x hx
    have h := card_nsmul_eq_zero' (G := ↥B ⧸ A.addSubgroupOf B)
      (x := ((⟨x, hx⟩ : B) : ↥B ⧸ A.addSubgroupOf B))
    rw [hcard, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf] at h
    simpa using h
  constructor
  · intro h σ ζ hζ a ha x hx
    obtain rfl := hζ.eq_neg_one_of_two_right
    rw [map_neg, map_one, eq_comm,
      neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : AlgebraicClosure ℚ) ≠ 1)] at ha
    obtain ⟨k, rfl⟩ := ha
    have := A.sub_mem (h σ x hx) (A.nsmul_mem (h2 x hx) k)
    convert this using 1
    rw [add_nsmul, one_nsmul, mul_nsmul]
    abel
  · intro h σ x hx
    simpa using h σ (-1) (IsPrimitiveRoot.neg_one 0 (by norm_num)) 1 (by simp) x hx

/-- Only tags count: `ZMod 2` with the trivial action also has the one-step chain with its step
tagged `false` (cyclotomic). Its quotient has trivial action, yet `filtAlpha` is `0`. -/
example :
    let c := zmodChain 2 false ((isTrivialStep_iff_isCyclotomicStep_two (trivialAction (ZMod 2))
      (natCard_top_quotient_bot 2)).mp (isTrivialStep_trivialAction ⊥ ⊤))
    filtAlpha c = 0 ∧
      ∀ i : Fin c.n, IsTrivialStep (trivialAction (ZMod 2)) (c.step i.castSucc) (c.step i.succ) :=
  ⟨rfl, fun _ => isTrivialStep_trivialAction _ _⟩
