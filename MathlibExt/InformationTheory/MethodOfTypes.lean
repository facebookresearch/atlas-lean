/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Data.Sym.Card
public import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# The method of types

For a finite alphabet `α` and a length `n`, the *type* of a sequence `x : Fin n → α` is its
empirical distribution. It is recorded here as the multiset of the letters of `x`, an element of
`Sym α n`, so the `n`-types are exactly the elements of `Sym α n` and the number of `a`'s in `x` is
`Multiset.count a (seqType x)`. The empirical distribution itself is
`empirical s a = count a s / n`, a probability vector for `n ≥ 1` (for `n = 0` it is the zero
function).

The basic counting lemmas of Csiszár ("The method of types", IEEE Trans. Inform. Theory 44 (1998),
Section II) are proved with the natural logarithm (the paper allows any base, used consistently):

* `card_sym_le_pow`: there are at most `(n + 1) ^ |α|` types (Lemma II.1 gives the exact count,
  which is Mathlib's `Sym.card_sym_eq_choose`);
* `card_typeClass_mul_prod_factorial`: the type class of `s` has `n! / ∏ₐ (count a s)!`
  elements;
* `prod_pow_count_eq_exp`: equation (II.1), `Qⁿ(x) = exp(-n (H(P) + D(P‖Q)))` for `x` of type `P`;
* `card_typeClass_le_exp`, `exp_le_card_sym_mul_card_typeClass`: the bounds (II.4) on `|T_P|`;
* `iidProb_typeClass_le_exp`, `exp_le_card_sym_mul_iidProb_typeClass`: the bounds (II.5) on
  `Qⁿ(T_P)`.

Probabilities of sets of sequences under `n` independent draws from `Q : α → ℝ` are written
`iidProb Q S = ∑_{x ∈ S} ∏ᵢ Q (x i)`; entropy and divergence are written as explicit finite sums
`∑ₐ negMulLog (P a)` and `∑ₐ P a * log (P a / Q a)`.
-/

@[expose] public section

namespace MathlibExt.InformationTheory.MethodOfTypes

open Finset Real

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-! ### Types and type classes -/

/-- **Type of a sequence.** The type of `x : Fin n → α` is the multiset of its letters, an element
of `Sym α n`; it records how often each letter occurs, which is the empirical distribution of `x`
up to the factor `1 / n` (Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998),
Section II). -/
def seqType (x : Fin n → α) : Sym α n :=
  ⟨univ.val.map x, by simp⟩

/-- **Type class.** The type class `T_s` of an `n`-type `s` is the set of sequences of length `n`
whose type is `s` (Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998),
Section II, before Lemma II.2). -/
def typeClass (s : Sym α n) : Finset (Fin n → α) :=
  univ.filter fun x => seqType x = s

/-- **Empirical distribution of a type.** The function `a ↦ count a s / n` of an `n`-type `s`.
For `n ≥ 1` it is a probability vector, and for `s = seqType x` it is the relative frequency of
each letter in `x` (Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998),
Section II). For `n = 0` it is the zero function, which is not a probability vector (every letter
gets `0`); the results that read it as a distribution assume `n ≠ 0`. -/
noncomputable def empirical (s : Sym α n) (a : α) : ℝ :=
  ((s : Multiset α).count a : ℝ) / n

/-- **Probability of a set of sequences under independent draws.** For `Q : α → ℝ` and a set `S` of
sequences of length `n`, `iidProb Q S = ∑_{x ∈ S} ∏ᵢ Q (xᵢ)`: when `Q` is a probability vector
this is the probability `Qⁿ(S)` that `n` independent draws from `Q` form a sequence in `S`
(Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), Section II). -/
noncomputable def iidProb (Q : α → ℝ) (S : Finset (Fin n → α)) : ℝ :=
  ∑ x ∈ S, ∏ i, Q (x i)

/-- **Membership in a type class.** `x ∈ T_s` exactly when the type of `x` is `s` (Csiszár, "The
method of types", IEEE Trans. Inform. Theory 44 (1998), Section II). -/
theorem mem_typeClass {s : Sym α n} {x : Fin n → α} : x ∈ typeClass s ↔ seqType x = s := by
  simp [typeClass]

omit [Fintype α] in
/-- **Letter counts of a sequence.** The number of `a`'s recorded by the type of `x` is the number
of positions `i` with `xᵢ = a` (Csiszár, "The method of types", IEEE Trans. Inform. Theory 44
(1998), Section II). -/
theorem count_seqType (x : Fin n → α) (a : α) :
    ((seqType x : Multiset α)).count a = Fintype.card {i // x i = a} := by
  simp only [seqType, Sym.coe_mk, Multiset.count_map, Fintype.card_subtype]
  rw [← Finset.filter_val, Finset.card_val]
  simp [eq_comm]

/-- **Letter counts add up to the length.** For an `n`-type `s`, `∑ₐ count a s = n` (Csiszár, "The
method of types", IEEE Trans. Inform. Theory 44 (1998), Section II). -/
theorem sum_count (s : Sym α n) : ∑ a, (s : Multiset α).count a = n := by
  have h := Multiset.toFinset_sum_count_eq (s : Multiset α)
  rw [Sym.card_coe] at h
  exact (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => by
    simpa using ha).symm.trans h

omit [Fintype α] in
/-- **A letter count is at most the length.** For an `n`-type `s`, `count a s ≤ n` (Csiszár, "The
method of types", IEEE Trans. Inform. Theory 44 (1998), Section II). -/
theorem count_le (s : Sym α n) (a : α) : (s : Multiset α).count a ≤ n := by
  have := Multiset.count_le_card a (s : Multiset α)
  rwa [Sym.card_coe] at this

/-- **Number of types.** There are at most `(n + 1) ^ |α|` types of sequences of length `n` over
`α`: a type is determined by its letter counts, each in `{0, …, n}`. Csiszár, "The method of
types", IEEE Trans. Inform. Theory 44 (1998), Lemma II.1, gives the exact count
`C(n + |α| - 1, |α| - 1)` (Mathlib's `Sym.card_sym_eq_choose`); this polynomial bound is the form
used in the exponential estimates. -/
theorem card_sym_le_pow : Fintype.card (Sym α n) ≤ (n + 1) ^ Fintype.card α := by
  have hinj : Function.Injective fun (s : Sym α n) (a : α) =>
      (⟨(s : Multiset α).count a, Nat.lt_succ_of_le (count_le s a)⟩ : Fin (n + 1)) := by
    intro s t h
    apply Subtype.ext
    ext a
    have := congrFun h a
    simpa using this
  simpa [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective _ hinj

omit [Fintype α] [DecidableEq α] in
/-- **Every type is realised.** Every `n`-type, that is every multiset of size `n`, is the type of
some sequence of length `n`, so type classes are nonempty (Csiszár, "The method of types", IEEE
Trans. Inform. Theory 44 (1998), Section II). -/
theorem exists_seqType_eq (s : Sym α n) : ∃ x : Fin n → α, seqType x = s := by
  obtain ⟨m, hm⟩ := s
  have hl : (m.toList).length = n := by simp [hm]
  refine ⟨fun i => m.toList.get (Fin.cast hl.symm i), ?_⟩
  apply Subtype.ext
  simp only [seqType, Fin.univ_val_map]
  conv_rhs => rw [← Multiset.coe_toList m]
  congr 1
  apply List.ext_get (by simp [hl])
  intro i h1 h2
  simp

omit [Fintype α] [DecidableEq α] in
/-- **Sequences of the same type are rearrangements.** Two sequences of length `n` with the same
type differ by a permutation of positions: `y ∘ σ = x` for some `σ` (Csiszár, "The method of types",
IEEE Trans. Inform. Theory 44 (1998), Section II). -/
theorem exists_perm_of_seqType_eq {x y : Fin n → α} (h : seqType x = seqType y) :
    ∃ σ : Equiv.Perm (Fin n), y ∘ σ = x := by
  let : DecidableEq α := Classical.decEq α
  have hc : ∀ a, Fintype.card {i // x i = a} = Fintype.card {i // y i = a} := fun a => by
    rw [← count_seqType, ← count_seqType, h]
  let e : ∀ a, {i // x i = a} ≃ {i // y i = a} := fun a => Fintype.equivOfCardEq (hc a)
  refine ⟨(Equiv.sigmaFiberEquiv x).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv y)), ?_⟩
  funext i
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaFiberEquiv_apply]
  exact ((e (x i)) ⟨i, rfl⟩).2

omit [Fintype α] [DecidableEq α] in
/-- **Permuting positions preserves the type.** `seqType (x ∘ σ) = seqType x` for every permutation
`σ` of positions (Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), Section II).
-/
theorem seqType_comp_perm (x : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    seqType (x ∘ σ) = seqType x := by
  apply Subtype.ext
  simp only [seqType]
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- **Size of a type class.** The type class of an `n`-type `s` has `n! / ∏ₐ (count a s)!`
elements, stated without division as `|T_s| · ∏ₐ (count a s)! = n!`. This is the multinomial
count behind Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), Lemma II.2
(and Csiszár–Shields, *Information Theory and Statistics: A Tutorial*, 2004, proof of
Lemma 2.2). -/
theorem card_typeClass_mul_prod_factorial (s : Sym α n) :
    #(typeClass s) * ∏ a, ((s : Multiset α).count a).factorial = n.factorial := by
  obtain ⟨x₀, hx₀⟩ := exists_seqType_eq s
  have hfib : ∀ y ∈ typeClass s,
      #(univ.filter fun σ : Equiv.Perm (Fin n) => x₀ ∘ σ = y) =
        ∏ a, ((s : Multiset α).count a).factorial := by
    intro y hy
    rw [mem_typeClass, ← hx₀] at hy
    obtain ⟨τ, hτ⟩ := exists_perm_of_seqType_eq hy
    -- `σ ↦ σ ∘ τ⁻¹` identifies the fibre over `y = x₀ ∘ τ` with the stabilizer of `x₀`
    have e : {σ : Equiv.Perm (Fin n) // x₀ ∘ σ = y} ≃ {g : Equiv.Perm (Fin n) // x₀ ∘ g = x₀} :=
      { toFun := fun σ => ⟨τ.symm.trans σ.1, by
          funext i
          have h1 := congrFun σ.2 (τ.symm i)
          have h2 := congrFun hτ (τ.symm i)
          simp only [Function.comp_apply, Equiv.apply_symm_apply] at h1 h2
          simp only [Function.comp_apply, Equiv.trans_apply]
          rw [h1, ← h2]⟩
        invFun := fun g => ⟨τ.trans g.1, by
          funext i
          have h1 := congrFun g.2 (τ i)
          have h2 := congrFun hτ i
          simp only [Function.comp_apply] at h1 h2
          simp only [Function.comp_apply, Equiv.trans_apply]
          rw [h1, h2]⟩
        left_inv := fun σ => by ext; simp
        right_inv := fun g => by ext; simp }
    rw [← Fintype.card_subtype, Fintype.card_congr e, DomMulAct.stabilizer_card]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← count_seqType, hx₀]
  have hmaps : ∀ σ ∈ (univ : Finset (Equiv.Perm (Fin n))), x₀ ∘ σ ∈ typeClass s := by
    intro σ _
    rw [mem_typeClass, seqType_comp_perm, hx₀]
  have := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin, Finset.sum_congr rfl hfib,
    Finset.sum_const, smul_eq_mul] at this
  exact this.symm

/-! ### Probability of a sequence -/

/-- **The probability of a sequence depends only on its type.** `∏ᵢ Q(xᵢ) = ∏ₐ Q(a) ^ nₐ`, where
`nₐ` is the number of `a`'s in `x` (Csiszár, "The method of types", IEEE Trans. Inform. Theory 44
(1998), first line of (II.1)). -/
theorem prod_apply_eq_prod_pow (Q : α → ℝ) (x : Fin n → α) :
    ∏ i, Q (x i) = ∏ a, Q a ^ ((seqType x : Multiset α)).count a := by
  rw [← Finset.prod_fiberwise univ x (fun i => Q (x i))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [count_seqType, Fintype.card_subtype]
  rw [Finset.prod_congr rfl (g := fun _ => Q a) (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
  simp

omit [DecidableEq α] in
/-- **Total mass of the product law.** `∑_{x ∈ αⁿ} ∏ᵢ Q(xᵢ) = (∑ₐ Q(a)) ^ n`, which is `1` when `Q`
is a probability vector (Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998),
Section II). -/
theorem iidProb_univ (Q : α → ℝ) : iidProb Q (univ : Finset (Fin n → α)) = (∑ a, Q a) ^ n := by
  rw [iidProb, Finset.sum_pow', Fintype.piFinset_univ]

omit [Fintype α] [DecidableEq α] in
/-- **Probabilities are nonnegative.** If `Q ≥ 0` then `Qⁿ(S) ≥ 0` for every set `S` of sequences
(Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), Section II). -/
theorem iidProb_nonneg {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a) (S : Finset (Fin n → α)) :
    0 ≤ iidProb Q S :=
  Finset.sum_nonneg fun x _ => Finset.prod_nonneg fun i _ => hQ (x i)

omit [Fintype α] [DecidableEq α] in
/-- **Monotonicity of the product law.** If `Q ≥ 0` and `S ⊆ T` then `Qⁿ(S) ≤ Qⁿ(T)` (Csiszár, "The
method of types", IEEE Trans. Inform. Theory 44 (1998), Section II). -/
theorem iidProb_mono {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a) {S T : Finset (Fin n → α)} (h : S ⊆ T) :
    iidProb Q S ≤ iidProb Q T :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun x _ _ => Finset.prod_nonneg fun i _ => hQ (x i)

/-- **Probability of a type class as size times probability of a sequence.**
`Qⁿ(T_s) = |T_s| · ∏ₐ Q(a) ^ (count a s)`, since all sequences of `T_s` are equiprobable
(Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), proof of Lemma II.2). -/
theorem iidProb_typeClass (Q : α → ℝ) (s : Sym α n) :
    iidProb Q (typeClass s) = #(typeClass s) * ∏ a, Q a ^ (s : Multiset α).count a := by
  rw [iidProb, Finset.sum_congr rfl (g := fun _ => ∏ a, Q a ^ (s : Multiset α).count a)
    (fun x hx => by rw [prod_apply_eq_prod_pow, mem_typeClass.mp hx])]
  simp

/-- **The type classes partition the sequences.** Summing `Qⁿ(T_s)` over all `n`-types `s` gives
`Qⁿ(αⁿ)` (Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), proof of
Lemma II.2). -/
theorem sum_iidProb_typeClass (Q : α → ℝ) :
    ∑ s : Sym α n, iidProb Q (typeClass s) = iidProb Q (univ : Finset (Fin n → α)) := by
  simp only [iidProb, typeClass]
  exact Finset.sum_fiberwise univ seqType _

omit [Fintype α] in
/-- **The empirical distribution is nonnegative** (Csiszár, "The method of types", IEEE Trans.
Inform. Theory 44 (1998), Section II). -/
theorem empirical_nonneg (s : Sym α n) (a : α) : 0 ≤ empirical s a := by
  unfold empirical; positivity

/-- **The empirical distribution sums to one.** For `n ≥ 1` and an `n`-type `s`, `∑ₐ count a s / n =
1` (Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), Section II). -/
theorem sum_empirical (hn : n ≠ 0) (s : Sym α n) : ∑ a, empirical s a = 1 := by
  simp only [empirical, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_count, mul_inv_cancel₀ (by exact_mod_cast hn)]

omit [Fintype α] in
/-- **Support of the empirical distribution.** For `n ≥ 1`, `count a s / n > 0` exactly when `a`
occurs in `s` (Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), Section II). -/
theorem empirical_pos_iff (hn : n ≠ 0) (s : Sym α n) (a : α) :
    0 < empirical s a ↔ 0 < (s : Multiset α).count a := by
  unfold empirical
  have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [div_pos_iff_of_pos_right this]
  exact_mod_cast Iff.rfl

omit [Fintype α] in
/-- **One letter of the sequence-probability formula.** With `k` the count of `a` in `s` and
`P(a) = k / n`, if `Q(a) > 0` whenever `k > 0`, then
`Q(a) ^ k = exp(-n (-P(a) log P(a) + P(a) log (P(a) / Q(a))))` (Csiszár, "The method of types",
IEEE Trans. Inform. Theory 44 (1998), (II.1), one factor). -/
theorem pow_count_eq_exp (hn : n ≠ 0) (s : Sym α n) {Q : α → ℝ} (a : α)
    (hQ : 0 < (s : Multiset α).count a → 0 < Q a) :
    Q a ^ (s : Multiset α).count a =
      exp (-(n : ℝ) * (negMulLog (empirical s a) +
        empirical s a * log (empirical s a / Q a))) := by
  rcases Nat.eq_zero_or_pos ((s : Multiset α).count a) with h0 | hpos
  · simp [h0, empirical]
  have hQa := hQ hpos
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hP : 0 < empirical s a := (empirical_pos_iff hn s a).mpr hpos
  have hk : (n : ℝ) * empirical s a = (s : Multiset α).count a := by
    unfold empirical; field_simp
  rw [negMulLog, log_div hP.ne' hQa.ne', ← exp_log (pow_pos hQa _), log_pow]
  congr 1
  rw [← hk]; ring

/-- **Probability of a sequence of a given type** (Csiszár, "The method of types", IEEE Trans.
Inform. Theory 44 (1998), equation (II.1)). If `x` has type `P` (the empirical distribution of
`s = seqType x`), `n ≥ 1`, and `Q(a) > 0` wherever `P(a) > 0`, then, with the natural logarithm,
`Qⁿ(x) = ∏ₐ Q(a) ^ (n P(a)) = exp(-n (H(P) + D(P ‖ Q)))`, where `H(P) = ∑ₐ -P(a) log P(a)` and
`D(P ‖ Q) = ∑ₐ P(a) log (P(a) / Q(a))`. The source states it for every `Q`, with `D = ∞` and both
sides `0` when the support condition fails; that case is `iidProb_typeClass_eq_zero`. -/
theorem prod_pow_count_eq_exp (hn : n ≠ 0) (s : Sym α n) {Q : α → ℝ}
    (hQ : ∀ a, 0 < (s : Multiset α).count a → 0 < Q a) :
    ∏ a, Q a ^ (s : Multiset α).count a =
      exp (-(n : ℝ) * (∑ a, negMulLog (empirical s a) +
        ∑ a, empirical s a * log (empirical s a / Q a))) := by
  rw [Finset.prod_congr rfl fun a _ => pow_count_eq_exp hn s a (hQ a), ← exp_sum,
    ← Finset.sum_add_distrib, Finset.mul_sum]

/-- **Probability of a sequence under its own type.** For `n ≥ 1` and the empirical distribution
`P` of `s`, `∏ₐ P(a) ^ (n P(a)) = exp(-n H(P))`: equation (II.1) of Csiszár, "The method of
types", IEEE Trans. Inform. Theory 44 (1998), with `Q = P`. -/
theorem prod_empirical_pow_count (hn : n ≠ 0) (s : Sym α n) :
    ∏ a, empirical s a ^ (s : Multiset α).count a =
      exp (-(n : ℝ) * ∑ a, negMulLog (empirical s a)) := by
  rw [prod_pow_count_eq_exp hn s fun a h => (empirical_pos_iff hn s a).mpr h]
  congr 2
  rw [add_eq_left]
  refine Finset.sum_eq_zero fun a _ => ?_
  rcases (empirical_nonneg s a).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [div_self h.ne', log_one, mul_zero]

/-- **Probability of a type class under its own type.** For `n ≥ 1` and the empirical
distribution `P` of `s`, `Pⁿ(T_s) = |T_s| exp(-n H(P))` (Csiszár, "The method of types", IEEE
Trans. Inform. Theory 44 (1998), proof of Lemma II.2). -/
theorem iidProb_empirical_typeClass (hn : n ≠ 0) (s : Sym α n) :
    iidProb (empirical s) (typeClass s) =
      #(typeClass s) * exp (-(n : ℝ) * ∑ a, negMulLog (empirical s a)) := by
  rw [iidProb_typeClass, prod_empirical_pow_count hn]

/-! ### Upper bounds -/

/-- **Upper bound on the size of a type class** (Csiszár, "The method of types", IEEE Trans.
Inform. Theory 44 (1998), Lemma II.2, right half of (II.4); Csiszár–Shields, *Information Theory
and Statistics: A Tutorial*, 2004, Lemma 2.2). For `n ≥ 1` and an `n`-type with empirical
distribution `P`, `|T_P| ≤ exp(n H(P))`, natural logarithm. -/
theorem card_typeClass_le_exp (hn : n ≠ 0) (s : Sym α n) :
    (#(typeClass s) : ℝ) ≤ exp ((n : ℝ) * ∑ a, negMulLog (empirical s a)) := by
  have h1 : iidProb (empirical s) (typeClass s) ≤ 1 := by
    calc iidProb (empirical s) (typeClass s) ≤ iidProb (empirical s) univ :=
          iidProb_mono (empirical_nonneg s) (subset_univ _)
      _ = 1 := by rw [iidProb_univ, sum_empirical hn, one_pow]
  rw [iidProb_empirical_typeClass hn, neg_mul, exp_neg, ← div_eq_mul_inv,
    div_le_one (exp_pos _)] at h1
  exact h1

/-- **Type classes outside the support have probability zero.** If some letter has positive count
in `s` but `Q`-probability zero, then `Qⁿ(T_s) = 0`; this is the case `D(P ‖ Q) = ∞` of (II.5)
in Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998). -/
theorem iidProb_typeClass_eq_zero (s : Sym α n) {Q : α → ℝ} {a : α}
    (ha : 0 < (s : Multiset α).count a) (hQa : Q a = 0) : iidProb Q (typeClass s) = 0 := by
  rw [iidProb_typeClass, Finset.prod_eq_zero (Finset.mem_univ a) (by rw [hQa, zero_pow ha.ne']),
    mul_zero]

/-- **Upper bound on the probability of a type class** (Csiszár, "The method of types", IEEE
Trans. Inform. Theory 44 (1998), Lemma II.2, right half of (II.5); Csiszár–Shields, *Information
Theory and Statistics: A Tutorial*, 2004, Lemma 2.3). For `n ≥ 1`, an `n`-type with empirical
distribution `P`, and any `Q ≥ 0`, `Qⁿ(T_P) ≤ exp(-n D(P ‖ Q))`, natural logarithm. When
`Q(a) = 0 < P(a)` for some `a`, the left side is `0` (the source's `D = ∞`), and the bound holds
for any value of the right side. -/
theorem iidProb_typeClass_le_exp (hn : n ≠ 0) (s : Sym α n) {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a) :
    iidProb Q (typeClass s) ≤
      exp (-(n : ℝ) * ∑ a, empirical s a * log (empirical s a / Q a)) := by
  by_cases hsupp : ∀ a, 0 < (s : Multiset α).count a → 0 < Q a
  · rw [iidProb_typeClass, prod_pow_count_eq_exp hn s hsupp, mul_add, exp_add, ← mul_assoc]
    refine mul_le_of_le_one_left (exp_pos _).le ?_
    have := card_typeClass_le_exp hn s
    rw [neg_mul, exp_neg, ← div_eq_mul_inv, div_le_one (exp_pos _)]
    exact this
  · push Not at hsupp
    obtain ⟨a, ha, hQa⟩ := hsupp
    rw [iidProb_typeClass_eq_zero s ha (le_antisymm hQa (hQ a))]
    exact (exp_pos _).le

/-! ### Lower bounds -/

/-- **A factorial inequality.** `k ^ j · k! ≤ k ^ k · j!` for all natural numbers `j, k`: the
coordinatewise inequality behind the maximality of `Pⁿ(T_P)` among type classes (Csiszár–Shields,
*Information Theory and Statistics: A Tutorial*, 2004, proof of Lemma 2.2). -/
theorem pow_mul_factorial_le (j k : ℕ) : k ^ j * k.factorial ≤ k ^ k * j.factorial := by
  rcases le_total j k with hjk | hkj
  · have h := Nat.factorial_mul_descFactorial (n := k) (k := k - j) (Nat.sub_le k j)
    rw [Nat.sub_sub_self hjk] at h
    rw [← h, ← Nat.pow_sub_mul_pow k hjk]
    calc k ^ j * (j.factorial * k.descFactorial (k - j))
        = k ^ j * j.factorial * k.descFactorial (k - j) := by ring
      _ ≤ k ^ j * j.factorial * k ^ (k - j) :=
          Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow k (k - j))
      _ = k ^ (k - j) * k ^ j * j.factorial := by ring
  · have h := Nat.factorial_mul_pow_le_factorial (m := k) (n := j - k)
    rw [Nat.add_sub_cancel' hkj] at h
    calc k ^ j * k.factorial = k ^ k * (k.factorial * k ^ (j - k)) := by
          rw [← Nat.pow_sub_mul_pow k hkj]; ring
      _ ≤ k ^ k * (k.factorial * (k + 1) ^ (j - k)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ k) _))
      _ ≤ k ^ k * j.factorial := Nat.mul_le_mul_left _ h

/-- **The type class of `P` is the most likely one under `Pⁿ`** (Csiszár, "The method of types",
IEEE Trans. Inform. Theory 44 (1998), proof of Lemma II.2; Csiszár–Shields, *Information Theory and
Statistics: A Tutorial*, 2004, proof of Lemma 2.2, "the largest term"). For `n`-types `s, t` with
`P` the empirical distribution of `s`, `Pⁿ(T_t) ≤ Pⁿ(T_s)`. -/
theorem iidProb_empirical_typeClass_le (s t : Sym α n) :
    iidProb (empirical s) (typeClass t) ≤ iidProb (empirical s) (typeClass s) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim t s]
  set k : α → ℕ := fun a => (s : Multiset α).count a
  set j : α → ℕ := fun a => (t : Multiset α).count a
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : ∀ m : α → ℕ, ∑ a, m a = n →
      ∏ a, empirical s a ^ m a = (∏ a, (k a : ℝ) ^ m a) / (n : ℝ) ^ n := by
    intro m hm
    simp only [empirical, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hm]
    rfl
  rw [iidProb_typeClass, iidProb_typeClass, hprod j (sum_count t), hprod k (sum_count s),
    ← mul_div_assoc, ← mul_div_assoc, div_le_div_iff_of_pos_right (pow_pos hnR n)]
  -- reduce to a statement about natural numbers
  have hT := card_typeClass_mul_prod_factorial t
  have hS := card_typeClass_mul_prod_factorial s
  set Fj : ℕ := ∏ a, (j a).factorial with hFj
  set Fk : ℕ := ∏ a, (k a).factorial with hFk
  set Pj : ℕ := ∏ a, (k a) ^ (j a) with hPj
  set Pk : ℕ := ∏ a, (k a) ^ (k a) with hPk
  have key : Pj * Fk ≤ Pk * Fj := by
    rw [hPj, hFk, hPk, hFj, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod fun a _ => pow_mul_factorial_le (j a) (k a)
  have hfac : 0 < Fj * Fk :=
    Nat.mul_pos (Finset.prod_pos fun a _ => Nat.factorial_pos _)
      (Finset.prod_pos fun a _ => Nat.factorial_pos _)
  have hnat : #(typeClass t) * Pj ≤ #(typeClass s) * Pk := by
    refine Nat.le_of_mul_le_mul_right ?_ hfac
    calc #(typeClass t) * Pj * (Fj * Fk) = (#(typeClass t) * Fj) * (Pj * Fk) := by ring
      _ ≤ (#(typeClass s) * Fk) * (Pk * Fj) := by
          rw [hT, hS]; exact Nat.mul_le_mul_left _ key
      _ = #(typeClass s) * Pk * (Fj * Fk) := by ring
  exact_mod_cast hnat

/-- **Lower bound on the size of a type class** (Csiszár, "The method of types", IEEE Trans.
Inform. Theory 44 (1998), Lemma II.2, left half of (II.4)). For `n ≥ 1` and an `n`-type with
empirical distribution `P`, `exp(n H(P)) ≤ |𝒫ₙ| · |T_P|`, where `|𝒫ₙ| = Fintype.card (Sym α n)` is
the number of `n`-types; natural logarithm. -/
theorem exp_le_card_sym_mul_card_typeClass (hn : n ≠ 0) (s : Sym α n) :
    exp ((n : ℝ) * ∑ a, negMulLog (empirical s a)) ≤
      Fintype.card (Sym α n) * (#(typeClass s) : ℝ) := by
  have h1 : (1 : ℝ) ≤ Fintype.card (Sym α n) * iidProb (empirical s) (typeClass s) := by
    calc (1 : ℝ) = iidProb (empirical s) univ := by
          rw [iidProb_univ, sum_empirical hn, one_pow]
      _ = ∑ t : Sym α n, iidProb (empirical s) (typeClass t) := (sum_iidProb_typeClass _).symm
      _ ≤ ∑ _t : Sym α n, iidProb (empirical s) (typeClass s) :=
          Finset.sum_le_sum fun t _ => iidProb_empirical_typeClass_le s t
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [iidProb_empirical_typeClass hn, neg_mul, exp_neg] at h1
  have he := exp_pos ((n : ℝ) * ∑ a, negMulLog (empirical s a))
  calc exp ((n : ℝ) * ∑ a, negMulLog (empirical s a))
      ≤ exp ((n : ℝ) * ∑ a, negMulLog (empirical s a)) *
          (Fintype.card (Sym α n) * (#(typeClass s) *
            (exp ((n : ℝ) * ∑ a, negMulLog (empirical s a)))⁻¹)) :=
        le_mul_of_one_le_right he.le h1
    _ = _ := by field_simp

/-- **Lower bound on the size of a type class, polynomial form** (Csiszár, "The method of types",
IEEE Trans. Inform. Theory 44 (1998), (II.4) combined with Lemma II.1). For `n ≥ 1` and an
`n`-type with empirical distribution `P`, `(n + 1)^{-|α|} exp(n H(P)) ≤ |T_P|`. -/
theorem exp_le_pow_mul_card_typeClass (hn : n ≠ 0) (s : Sym α n) :
    exp ((n : ℝ) * ∑ a, negMulLog (empirical s a)) ≤
      ((n : ℝ) + 1) ^ Fintype.card α * #(typeClass s) := by
  refine (exp_le_card_sym_mul_card_typeClass hn s).trans
    (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
  exact_mod_cast card_sym_le_pow

/-- **Lower bound on the probability of a type class** (Csiszár, "The method of types", IEEE
Trans. Inform. Theory 44 (1998), Lemma II.2, left half of (II.5); Csiszár–Shields, *Information
Theory and Statistics: A Tutorial*, 2004, Lemma 2.3). For `n ≥ 1`, an `n`-type with empirical
distribution `P`, and `Q` with `Q(a) > 0` wherever `P(a) > 0`,
`exp(-n D(P ‖ Q)) ≤ |𝒫ₙ| · Qⁿ(T_P)`, natural logarithm. -/
theorem exp_le_card_sym_mul_iidProb_typeClass (hn : n ≠ 0) (s : Sym α n) {Q : α → ℝ}
    (hQ : ∀ a, 0 < empirical s a → 0 < Q a) :
    exp (-(n : ℝ) * ∑ a, empirical s a * log (empirical s a / Q a)) ≤
      Fintype.card (Sym α n) * iidProb Q (typeClass s) := by
  have hQ' : ∀ a, 0 < (s : Multiset α).count a → 0 < Q a :=
    fun a h => hQ a ((empirical_pos_iff hn s a).mpr h)
  rw [iidProb_typeClass, prod_pow_count_eq_exp hn s hQ', mul_add, exp_add]
  have h := exp_le_card_sym_mul_card_typeClass hn s
  set H := ∑ a, negMulLog (empirical s a)
  set D := ∑ a, empirical s a * log (empirical s a / Q a)
  have : exp (-(n : ℝ) * H) * exp ((n : ℝ) * H) = 1 := by rw [← exp_add]; simp
  calc exp (-(n : ℝ) * D) = exp (-(n : ℝ) * D) * (exp (-(n : ℝ) * H) * exp ((n : ℝ) * H)) := by
        rw [this, mul_one]
    _ ≤ exp (-(n : ℝ) * D) * (exp (-(n : ℝ) * H) * (Fintype.card (Sym α n) * #(typeClass s))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (exp_pos _).le) (exp_pos _).le
    _ = _ := by ring

/-- **Lower bound on the probability of a type class, polynomial form** (Csiszár, "The method of
types", IEEE Trans. Inform. Theory 44 (1998), (II.5) combined with Lemma II.1). For `n ≥ 1`, an
`n`-type with empirical distribution `P`, and `Q` with `Q(a) > 0` wherever `P(a) > 0`,
`(n + 1)^{-|α|} exp(-n D(P ‖ Q)) ≤ Qⁿ(T_P)`. -/
theorem exp_le_pow_mul_iidProb_typeClass (hn : n ≠ 0) (s : Sym α n) {Q : α → ℝ}
    (hQ0 : ∀ a, 0 ≤ Q a) (hQ : ∀ a, 0 < empirical s a → 0 < Q a) :
    exp (-(n : ℝ) * ∑ a, empirical s a * log (empirical s a / Q a)) ≤
      ((n : ℝ) + 1) ^ Fintype.card α * iidProb Q (typeClass s) := by
  refine (exp_le_card_sym_mul_iidProb_typeClass hn s hQ).trans
    (mul_le_mul_of_nonneg_right ?_ (iidProb_nonneg hQ0 _))
  exact_mod_cast card_sym_le_pow

end MathlibExt.InformationTheory.MethodOfTypes
