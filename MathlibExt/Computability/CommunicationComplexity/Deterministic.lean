/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Deterministic two-party communication complexity

Yao's model of two-party communication (A. C. Yao, "Some complexity questions related to
distributive computing", STOC 1979). Alice holds `x : X`, Bob holds `y : Y`, and they want to
compute a Boolean function `f : X → Y → Bool`. A deterministic protocol is a binary tree whose
internal nodes are owned by Alice or by Bob and labelled by a predicate on that party's input,
and whose leaves are labelled by the output; its cost is the depth of the tree.

Main results, following A. Rao and A. Yehudayoff, *Communication Complexity* (early draft,
Chapters 1 and 2) and S. Arora and B. Barak, *Computational Complexity: A Modern Approach*
(web draft of 2007-01-08, Chapter 12):

* `Protocol.card_leaves_le`: a protocol of depth `d` has at most `2 ^ d` leaves;
* `Protocol.transcript_eq_iff`: the inputs reaching a given leaf form a combinatorial
  rectangle (the rectangle lemma);
* `Protocol.card_le_two_pow_of_isFoolingSet`: the fooling-set lower bound;
* `Protocol.rank_le_two_pow_depth` and `log_rank_le_commComplexity`: the rank lower bound
  `rank M_f ≤ 2 ^ D(f)`, that is `D(f) ≥ ⌈log₂ rank M_f⌉`;
* `commComplexity_eqFn`: the equality function on `n ≥ 1` bits has deterministic
  communication complexity exactly `n + 1`;
* `LogRankConjecture`: the log-rank conjecture of Lovász and Saks, as a proposition only.
-/

@[expose] public section

namespace MathlibExt.Computability.CommunicationComplexity

/-- **Deterministic two-party protocol.** A protocol for inputs `x : X` (held by Alice) and
`y : Y` (held by Bob) is a binary tree: a leaf `output b` announces the Boolean `b`; a node
`alice f p₀ p₁` has Alice announce the bit `f x` and continue with `p₀` or `p₁` accordingly;
a node `bob g p₀ p₁` has Bob announce `g y` (A. Rao and A. Yehudayoff, *Communication
Complexity*, early draft, Chapter 1, "Defining 2 party protocols"; A. C. Yao, STOC 1979). -/
inductive Protocol (X Y : Type*) where
  /-- A leaf, labelled by the output. -/
  | output (b : Bool) : Protocol X Y
  /-- Alice announces `f x` and the protocol continues with `p₀` (bit `false`) or `p₁`. -/
  | alice (f : X → Bool) (p₀ p₁ : Protocol X Y) : Protocol X Y
  /-- Bob announces `g y` and the protocol continues with `p₀` (bit `false`) or `p₁`. -/
  | bob (g : Y → Bool) (p₀ p₁ : Protocol X Y) : Protocol X Y

namespace Protocol

variable {X Y : Type*}

/-- **Output of a protocol.** The label of the leaf reached when Alice holds `x` and Bob
holds `y`. -/
def eval : Protocol X Y → X → Y → Bool
  | output b, _, _ => b
  | alice f p₀ p₁, x, y => if f x then p₁.eval x y else p₀.eval x y
  | bob g p₀ p₁, x, y => if g y then p₁.eval x y else p₀.eval x y

/-- **Communication cost of a protocol.** The depth of its tree: the largest number of bits
exchanged on any input. -/
def depth : Protocol X Y → ℕ
  | output _ => 0
  | alice _ p₀ p₁ => max p₀.depth p₁.depth + 1
  | bob _ p₀ p₁ => max p₀.depth p₁.depth + 1

/-- **A protocol computes a function.** `p.Computes f` when the output of `p` on every input
pair `(x, y)` is `f x y`. -/
def Computes (p : Protocol X Y) (f : X → Y → Bool) : Prop :=
  ∀ x y, p.eval x y = f x y

/-- **Transcript of a protocol.** The list of bits announced on inputs `(x, y)`; it names the
root-to-leaf path the run follows. -/
def transcript : Protocol X Y → X → Y → List Bool
  | output _, _, _ => []
  | alice f p₀ p₁, x, y => f x :: if f x then p₁.transcript x y else p₀.transcript x y
  | bob g p₀ p₁, x, y => g y :: if g y then p₁.transcript x y else p₀.transcript x y

/-- **Leaves of a protocol tree.** The set of root-to-leaf paths, each written as the list of
bits announced along it. -/
def leaves : Protocol X Y → Finset (List Bool)
  | output _ => {[]}
  | alice _ p₀ p₁ =>
      p₀.leaves.map ⟨List.cons false, List.cons_injective⟩ ∪
        p₁.leaves.map ⟨List.cons true, List.cons_injective⟩
  | bob _ p₀ p₁ =>
      p₀.leaves.map ⟨List.cons false, List.cons_injective⟩ ∪
        p₁.leaves.map ⟨List.cons true, List.cons_injective⟩

private theorem card_union_map_le (A B : Finset (List Bool)) (a b : ℕ)
    (hA : A.card ≤ 2 ^ a) (hB : B.card ≤ 2 ^ b) :
    (A.map ⟨List.cons false, List.cons_injective⟩ ∪
        B.map ⟨List.cons true, List.cons_injective⟩).card ≤ 2 ^ (max a b + 1) := by
  refine (Finset.card_union_le _ _).trans ?_
  rw [Finset.card_map, Finset.card_map, pow_succ]
  have ha : 2 ^ a ≤ 2 ^ max a b := Nat.pow_le_pow_right (by norm_num) (le_max_left a b)
  have hb : 2 ^ b ≤ 2 ^ max a b := Nat.pow_le_pow_right (by norm_num) (le_max_right a b)
  omega

/-- **A protocol of depth `d` has at most `2 ^ d` leaves** (A. Rao and A. Yehudayoff,
*Communication Complexity*, early draft, Lemma 1.2). -/
theorem card_leaves_le (p : Protocol X Y) : p.leaves.card ≤ 2 ^ p.depth := by
  induction p with
  | output b => simp [leaves, depth]
  | alice f p₀ p₁ h₀ h₁ => exact card_union_map_le _ _ _ _ h₀ h₁
  | bob g p₀ p₁ h₀ h₁ => exact card_union_map_le _ _ _ _ h₀ h₁

/-- **Transcripts are leaf paths.** The transcript of every run is the path of a leaf of the
protocol tree. -/
theorem transcript_mem_leaves (p : Protocol X Y) (x : X) (y : Y) :
    p.transcript x y ∈ p.leaves := by
  induction p with
  | output b => simp [transcript, leaves]
  | alice f p₀ p₁ h₀ h₁ =>
    cases hf : f x <;> simp [transcript, leaves, hf, h₀, h₁]
  | bob g p₀ p₁ h₀ h₁ =>
    cases hg : g y <;> simp [transcript, leaves, hg, h₀, h₁]

/-- **The output is determined by the transcript.** Two runs with the same transcript end at
the same leaf, so they produce the same output. -/
theorem eval_eq_of_transcript_eq (p : Protocol X Y) {x x' : X} {y y' : Y}
    (h : p.transcript x y = p.transcript x' y') : p.eval x y = p.eval x' y' := by
  induction p with
  | output b => rfl
  | alice f p₀ p₁ h₀ h₁ =>
    simp only [transcript, List.cons.injEq] at h
    obtain ⟨hf, ht⟩ := h
    simp only [eval, ← hf]
    rw [← hf] at ht
    cases hfx : f x <;> simp only [hfx, Bool.false_eq_true, ↓reduceIte] at ht ⊢
    · exact h₀ ht
    · exact h₁ ht
  | bob g p₀ p₁ h₀ h₁ =>
    simp only [transcript, List.cons.injEq] at h
    obtain ⟨hg, ht⟩ := h
    simp only [eval, ← hg]
    rw [← hg] at ht
    cases hgy : g y <;> simp only [hgy, Bool.false_eq_true, ↓reduceIte] at ht ⊢
    · exact h₀ ht
    · exact h₁ ht

/-- **Crossing property of transcripts.** If the runs on `(x, y)` and `(x', y')` have the same
transcript, then so does the run on the crossed pair `(x, y')`. -/
theorem transcript_cross (p : Protocol X Y) {x x' : X} {y y' : Y}
    (h : p.transcript x y = p.transcript x' y') : p.transcript x y' = p.transcript x y := by
  induction p with
  | output b => rfl
  | alice f p₀ p₁ h₀ h₁ =>
    simp only [transcript, List.cons.injEq] at h
    obtain ⟨hf, ht⟩ := h
    simp only [transcript]
    congr 1
    rw [← hf] at ht
    cases hfx : f x <;> simp only [hfx, Bool.false_eq_true, ↓reduceIte] at ht ⊢
    · exact h₀ ht
    · exact h₁ ht
  | bob g p₀ p₁ h₀ h₁ =>
    simp only [transcript, List.cons.injEq] at h
    obtain ⟨hg, ht⟩ := h
    simp only [transcript]
    rw [← hg]
    congr 1
    rw [← hg] at ht
    cases hgy : g y <;> simp only [hgy, Bool.false_eq_true, ↓reduceIte] at ht ⊢
    · exact h₀ ht
    · exact h₁ ht

/-- **Rectangle lemma.** The inputs on which a protocol follows a given path `π` form a
combinatorial rectangle `A × B`, with `A` the inputs of Alice that reach `π` against some input
of Bob and `B` symmetrically (A. Rao and A. Yehudayoff, *Communication Complexity*, early
draft, Lemmas 1.5 and 1.6). -/
theorem transcript_eq_iff (p : Protocol X Y) (π : List Bool) (x : X) (y : Y) :
    p.transcript x y = π ↔
      (∃ y', p.transcript x y' = π) ∧ ∃ x', p.transcript x' y = π := by
  refine ⟨fun h => ⟨⟨y, h⟩, ⟨x, h⟩⟩, ?_⟩
  rintro ⟨⟨y', hy'⟩, ⟨x', hx'⟩⟩
  rw [p.transcript_cross (hy'.trans hx'.symm), hy']

/-- **Leaf rectangles are monochromatic.** If a protocol computes `f`, then `f` takes the same
value on any two input pairs that reach the same leaf, and on the crossed pair (A. Rao and
A. Yehudayoff, *Communication Complexity*, early draft, Theorem 1.7). -/
theorem eq_of_transcript_eq {f : X → Y → Bool} {p : Protocol X Y} (hp : p.Computes f)
    {x x' : X} {y y' : Y} (h : p.transcript x y = p.transcript x' y') :
    f x y' = f x y ∧ f x' y' = f x y := by
  refine ⟨?_, ?_⟩
  · rw [← hp, ← hp]; exact p.eval_eq_of_transcript_eq (p.transcript_cross h)
  · rw [← hp, ← hp]; exact (p.eval_eq_of_transcript_eq h).symm

/-- **Fooling set.** A finite set `S` of input pairs is a fooling set for `f` with value `b`
when `f = b` on `S` and, for any two distinct pairs `(x₁, y₁)` and `(x₂, y₂)` of `S`, either
`f x₁ y₂ ≠ b` or `f x₂ y₁ ≠ b` (S. Arora and B. Barak, *Computational Complexity*, web draft of
2007-01-08, Definition 12.3). -/
def IsFoolingSet (f : X → Y → Bool) (S : Finset (X × Y)) (b : Bool) : Prop :=
  (∀ s ∈ S, f s.1 s.2 = b) ∧
    ∀ s ∈ S, ∀ t ∈ S, s ≠ t → f s.1 t.2 ≠ b ∨ f t.1 s.2 ≠ b

/-- **Fooling-set pairs reach distinct leaves.** If a protocol computes `f`, distinct pairs of
a fooling set for `f` have distinct transcripts (S. Arora and B. Barak, *Computational
Complexity*, web draft of 2007-01-08, proof of Lemma 12.4). -/
theorem injOn_transcript_of_isFoolingSet {f : X → Y → Bool} {p : Protocol X Y}
    (hp : p.Computes f) {S : Finset (X × Y)} {b : Bool} (hS : IsFoolingSet f S b) :
    Set.InjOn (fun s : X × Y => p.transcript s.1 s.2) S := by
  intro s hs t ht hst
  by_contra hne
  have h₁ := eq_of_transcript_eq hp (x := s.1) (y := s.2) (x' := t.1) (y' := t.2) hst
  have h₂ := eq_of_transcript_eq hp (x := t.1) (y := t.2) (x' := s.1) (y' := s.2) hst.symm
  rcases hS.2 s hs t ht hne with h | h
  · exact h (h₁.1.trans (hS.1 s hs))
  · exact h (h₂.1.trans (hS.1 t ht))

/-- **Fooling-set lower bound.** If `f` has a fooling set `S`, every protocol computing `f`
has depth `d` with `|S| ≤ 2 ^ d` (S. Arora and B. Barak, *Computational Complexity*, web draft
of 2007-01-08, Lemma 12.4). -/
theorem card_le_two_pow_of_isFoolingSet {f : X → Y → Bool} {p : Protocol X Y}
    (hp : p.Computes f) {S : Finset (X × Y)} {b : Bool} (hS : IsFoolingSet f S b) :
    S.card ≤ 2 ^ p.depth :=
  (Finset.card_le_card_of_injOn _ (fun s _ => p.transcript_mem_leaves s.1 s.2)
    (injOn_transcript_of_isFoolingSet hp hS)).trans p.card_leaves_le

/-- **Communication matrix.** The matrix of `f : X → Y → Bool` over a ring `K`, with entry `1`
at `(x, y)` when `f x y` holds and `0` otherwise. -/
def commMatrix (K : Type*) [Zero K] [One K] (f : X → Y → Bool) : Matrix X Y K :=
  fun x y => if f x y then 1 else 0

open Classical in
/-- **Rank lower bound.** Over any field `K`, if a protocol of depth `d` computes `f`, then the
communication matrix of `f` has rank at most `2 ^ d`; equivalently `d ≥ log₂ rank M_f`
(A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Lemma 2.10 and
Theorem 2.11; S. Arora and B. Barak, *Computational Complexity*, web draft of 2007-01-08,
Theorem 12.10 `χ(f) ≥ rank M(f)` with Theorem 12.7 `C(f) ≥ log₂ χ(f)`). -/
theorem rank_le_two_pow_depth [Fintype Y] {K : Type*} [Field K]
    {f : X → Y → Bool} {p : Protocol X Y} (hp : p.Computes f) :
    (commMatrix K f).rank ≤ 2 ^ p.depth := by
  let U : Matrix X p.leaves K := fun x π => if ∃ y, p.transcript x y = π.1 then 1 else 0
  let V : Matrix p.leaves Y K := fun π y =>
    if ∃ x, p.transcript x y = π.1 ∧ p.eval x y = true then 1 else 0
  have hUV : U * V = commMatrix K f := by
    ext x y
    rw [Matrix.mul_apply, Finset.sum_eq_single ⟨p.transcript x y, p.transcript_mem_leaves x y⟩]
    · have hV : (∃ x', p.transcript x' y = p.transcript x y ∧ p.eval x' y = true) ↔
          p.eval x y = true :=
        ⟨fun ⟨x', h, he⟩ => (p.eval_eq_of_transcript_eq h).symm.trans he,
          fun he => ⟨x, rfl, he⟩⟩
      have hU : ∃ y', p.transcript x y' = p.transcript x y := ⟨y, rfl⟩
      simp only [U, V, commMatrix, ← hp x y, hU, hV, ite_true, one_mul]
    · intro π _ hπ
      simp only [U, V]
      by_cases hA : ∃ y', p.transcript x y' = π.1
      · by_cases hB : ∃ x', p.transcript x' y = π.1 ∧ p.eval x' y = true
        · exfalso
          obtain ⟨x', hx', -⟩ := hB
          exact hπ (Subtype.ext ((p.transcript_eq_iff π.1 x y).2 ⟨hA, ⟨x', hx'⟩⟩).symm)
        · simp only [hB, ite_false, mul_zero]
      · simp only [hA, ite_false, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [← hUV]
  refine (Matrix.rank_mul_le_left U V).trans ((Matrix.rank_le_card_width U).trans ?_)
  rw [Fintype.card_coe]
  exact p.card_leaves_le

/-- **Alice reveals her input from a list.** Alice walks down a list of candidates, announcing
for each whether it is her input; the protocol continues with `k a` for the revealed candidate
`a`, and inputs not in the list end at the output `false`. -/
def aliceReveal [DecidableEq X] : List X → (X → Protocol X Y) → Protocol X Y
  | [], _ => output false
  | a :: l, k => alice (fun x => decide (x = a)) (aliceReveal l k) (k a)

/-- **Bob reveals his input from a list.** The analogue of `aliceReveal` for Bob. -/
def bobReveal [DecidableEq Y] : List Y → (Y → Protocol X Y) → Protocol X Y
  | [], _ => output false
  | b :: l, k => bob (fun y => decide (y = b)) (bobReveal l k) (k b)

/-- **Alice reveals her input.** If `x` is in the candidate list, the run of `aliceReveal l k`
on `(x, y)` ends as the run of `k x` does. -/
theorem eval_aliceReveal [DecidableEq X] (l : List X) (k : X → Protocol X Y) {x : X}
    (hx : x ∈ l) (y : Y) : (aliceReveal l k).eval x y = (k x).eval x y := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    by_cases h : x = a
    · subst h; simp [aliceReveal, eval]
    · simp only [aliceReveal, eval, h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih (by simpa [h] using hx)

/-- **Bob reveals his input.** If `y` is in the candidate list, the run of `bobReveal l k` on
`(x, y)` ends as the run of `k y` does. -/
theorem eval_bobReveal [DecidableEq Y] (l : List Y) (k : Y → Protocol X Y) (x : X) {y : Y}
    (hy : y ∈ l) : (bobReveal l k).eval x y = (k y).eval x y := by
  induction l with
  | nil => simp at hy
  | cons b l ih =>
    by_cases h : y = b
    · subst h; simp [bobReveal, eval]
    · simp only [bobReveal, eval, h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih (by simpa [h] using hy)

/-- **Every function on finite inputs has a protocol**: Alice reveals `x`, then Bob reveals
`y`, and the leaf reached is labelled `f x y`. -/
theorem exists_computes [Finite X] [Finite Y] (f : X → Y → Bool) :
    ∃ p : Protocol X Y, p.Computes f := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  exact ⟨aliceReveal Finset.univ.toList fun a =>
      bobReveal Finset.univ.toList fun b => output (f a b),
    fun x y => by
      rw [eval_aliceReveal _ _ (Finset.mem_toList.2 (Finset.mem_univ x)),
        eval_bobReveal _ _ _ (Finset.mem_toList.2 (Finset.mem_univ y))]
      rfl⟩

/-- **Alice sends a `b`-bit message.** Alice announces the `b` bits of the message `v x`, one at a
time, and the protocol then continues with `k m` for the announced message `m`. -/
def aliceSends : (b : ℕ) → (X → Fin b → Bool) → ((Fin b → Bool) → Protocol X Y) → Protocol X Y
  | 0, _, k => k Fin.elim0
  | b + 1, v, k =>
      alice (fun x => v x 0)
        (aliceSends b (fun x i => v x i.succ) fun m => k (Fin.cons false m))
        (aliceSends b (fun x i => v x i.succ) fun m => k (Fin.cons true m))

/-- **Output after Alice sends a message.** The run of `aliceSends b v k` on `(x, y)` ends as
the run of `k (v x)` does. -/
theorem eval_aliceSends (b : ℕ) (v : X → Fin b → Bool) (k : (Fin b → Bool) → Protocol X Y)
    (x : X) (y : Y) : (aliceSends b v k).eval x y = (k (v x)).eval x y := by
  induction b with
  | zero => simp only [aliceSends]; congr; funext i; exact i.elim0
  | succ b ih =>
    have hv : (Fin.cons (v x 0) fun i => v x i.succ : Fin (b + 1) → Bool) = v x :=
      Fin.cons_self_tail (v x)
    have key : (aliceSends (b + 1) v k).eval x y =
        (k (Fin.cons (v x 0) fun i => v x i.succ)).eval x y := by
      cases h0 : v x 0 <;> simp [aliceSends, eval, h0, ih]
    rw [key, hv]

/-- **Cost of sending a `b`-bit message.** If every continuation costs at most `d` bits, then
`aliceSends b v k` costs at most `b + d` bits. -/
theorem depth_aliceSends_le (b : ℕ) (v : X → Fin b → Bool) (k : (Fin b → Bool) → Protocol X Y)
    {d : ℕ} (hk : ∀ m, (k m).depth ≤ d) : (aliceSends b v k).depth ≤ b + d := by
  induction b generalizing d with
  | zero => simpa [aliceSends] using hk Fin.elim0
  | succ b ih =>
    simp only [aliceSends, depth]
    have h₀ := ih (fun x i => v x i.succ) (fun m => k (Fin.cons false m)) (fun m => hk _)
    have h₁ := ih (fun x i => v x i.succ) (fun m => k (Fin.cons true m)) (fun m => hk _)
    omega

end Protocol

open Protocol

/-- **Deterministic communication complexity.** `commComplexity f` is the least depth of a
protocol computing `f : X → Y → Bool` (A. C. Yao, STOC 1979; A. Rao and A. Yehudayoff,
*Communication Complexity*, early draft, Chapter 1). For finite inputs such a protocol always
exists (`Protocol.exists_computes`). If no protocol computes `f`, which is possible only for
infinite inputs, the value is `0` by the convention `sInf ∅ = 0`. -/
noncomputable def commComplexity {X Y : Type*} (f : X → Y → Bool) : ℕ :=
  sInf {d | ∃ p : Protocol X Y, p.Computes f ∧ p.depth = d}

variable {X Y : Type*} [Finite X] [Finite Y]

/-- **An optimal protocol exists.** For finite inputs, some protocol computing `f` has depth
exactly `commComplexity f`. -/
theorem exists_depth_eq_commComplexity (f : X → Y → Bool) :
    ∃ p : Protocol X Y, p.Computes f ∧ p.depth = commComplexity f := by
  obtain ⟨p, hp⟩ := Protocol.exists_computes f
  exact Nat.sInf_mem (s := {d | ∃ p : Protocol X Y, p.Computes f ∧ p.depth = d}) ⟨_, p, hp, rfl⟩

omit [Finite X] [Finite Y] in
/-- **Every protocol costs at least `D(f)`.** Every protocol computing `f` has depth at least
`commComplexity f`. -/
theorem commComplexity_le_depth {f : X → Y → Bool} {p : Protocol X Y} (hp : p.Computes f) :
    commComplexity f ≤ p.depth :=
  Nat.sInf_le ⟨p, hp, rfl⟩

/-- **Fooling-set lower bound for `D(f)`.** If `f` has a fooling set `S`, then
`|S| ≤ 2 ^ D(f)`, that is `D(f) ≥ log₂ |S|` (S. Arora and B. Barak, *Computational
Complexity*, web draft of 2007-01-08, Lemma 12.4). -/
theorem card_le_two_pow_commComplexity {f : X → Y → Bool} {S : Finset (X × Y)} {b : Bool}
    (hS : IsFoolingSet f S b) : S.card ≤ 2 ^ commComplexity f := by
  obtain ⟨p, hp, hd⟩ := exists_depth_eq_commComplexity f
  rw [← hd]
  exact card_le_two_pow_of_isFoolingSet hp hS

/-- **Rank lower bound for `D(f)`.** Over any field `K`, `rank M_f ≤ 2 ^ D(f)` (A. Rao and
A. Yehudayoff, *Communication Complexity*, early draft, Lemma 2.10 with Theorem 1.7). -/
theorem rank_le_two_pow_commComplexity [Fintype Y] (K : Type*) [Field K] (f : X → Y → Bool) :
    (commMatrix K f).rank ≤ 2 ^ commComplexity f := by
  obtain ⟨p, hp, hd⟩ := exists_depth_eq_commComplexity f
  rw [← hd]
  exact rank_le_two_pow_depth hp

/-- **Log-rank lower bound.** Over any field `K`, `⌈log₂ rank M_f⌉ ≤ D(f)`; since `D(f)` is an
integer, this is `log₂ rank M_f ≤ D(f)` (A. Rao and A. Yehudayoff, *Communication Complexity*,
early draft, Theorem 2.11: "If a matrix has rank `r`, then its communication complexity is at
least `log r`"). -/
theorem log_rank_le_commComplexity [Fintype Y] (K : Type*) [Field K] (f : X → Y → Bool) :
    Nat.clog 2 (commMatrix K f).rank ≤ commComplexity f :=
  Nat.clog_le_of_le_pow (rank_le_two_pow_commComplexity K f)

/-- **Equality function.** `eqFn n x y` holds exactly when the `n`-bit strings `x` and `y` are
equal. -/
def eqFn (n : ℕ) (x y : Fin n → Bool) : Bool :=
  decide (x = y)

/-- **The trivial protocol for equality.** Alice sends her `n` bits and Bob announces whether
they equal his input: `n + 1` bits. -/
def eqProtocol (n : ℕ) : Protocol (Fin n → Bool) (Fin n → Bool) :=
  aliceSends n id fun m => bob (fun y => decide (m = y)) (output false) (output true)

/-- **The trivial protocol computes equality.** -/
theorem eqProtocol_computes (n : ℕ) : (eqProtocol n).Computes (eqFn n) := by
  intro x y
  rw [eqProtocol, eval_aliceSends]
  by_cases h : x = y <;> simp [eval, eqFn, h]

/-- **Upper bound for equality.** The trivial protocol costs at most `n + 1` bits (A. Rao and
A. Yehudayoff, *Communication Complexity*, early draft, Chapter 1: "Alice can send Bob her
input, and Bob can respond with the value of a function, giving a protocol with communication
`n + 1`"). -/
theorem depth_eqProtocol_le (n : ℕ) : (eqProtocol n).depth ≤ n + 1 :=
  depth_aliceSends_le _ _ _ fun _ => by simp [depth]

/-- **Lower bound for equality.** For `n ≥ 1`, every protocol computing equality of `n`-bit
strings has depth at least `n + 1`: the `2 ^ n` diagonal pairs reach distinct leaves with
output `1`, and some other leaf has output `0` (A. Rao and A. Yehudayoff, *Communication
Complexity*, early draft, Claim 1.13 and Theorem 1.14). -/
theorem lt_depth_of_computes_eqFn {n : ℕ} (hn : 1 ≤ n)
    {p : Protocol (Fin n → Bool) (Fin n → Bool)} (hp : p.Computes (eqFn n)) :
    n < p.depth := by
  classical
  let T : Finset (List Bool) := Finset.univ.image fun x => p.transcript x x
  have hinj : Function.Injective fun x : Fin n → Bool => p.transcript x x := by
    intro x x' h
    have := (eq_of_transcript_eq hp h).1
    simpa [eqFn] using this
  have hT : T.card = 2 ^ n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  let x₀ : Fin n → Bool := fun _ => false
  let y₀ : Fin n → Bool := fun _ => true
  have hxy : x₀ ≠ y₀ := fun h => by simpa [x₀, y₀] using congrFun h ⟨0, hn⟩
  have hnot : p.transcript x₀ y₀ ∉ T := by
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro x hx
    have := p.eval_eq_of_transcript_eq hx
    rw [hp, hp] at this
    simp [eqFn, hxy] at this
  have hsub : insert (p.transcript x₀ y₀) T ⊆ p.leaves := by
    intro π hπ
    rcases Finset.mem_insert.1 hπ with rfl | hπ
    · exact p.transcript_mem_leaves _ _
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hπ
      exact p.transcript_mem_leaves _ _
  have hcard := (Finset.card_le_card hsub).trans p.card_leaves_le
  rw [Finset.card_insert_of_notMem hnot, hT] at hcard
  by_contra h
  have : 2 ^ p.depth ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (not_lt.1 h)
  omega

/-- **Deterministic communication complexity of equality.** For `n ≥ 1`, equality of `n`-bit
strings has deterministic communication complexity exactly `n + 1` (A. Rao and A. Yehudayoff,
*Communication Complexity*, early draft, Theorem 1.14, with the trivial protocol for the upper
bound). For `n = 0` the function is constant and the complexity is `0`. -/
theorem commComplexity_eqFn {n : ℕ} (hn : 1 ≤ n) : commComplexity (eqFn n) = n + 1 := by
  obtain ⟨p, hp, hd⟩ := exists_depth_eq_commComplexity (eqFn n)
  have h₁ := lt_depth_of_computes_eqFn hn hp
  have h₂ := (commComplexity_le_depth (eqProtocol_computes n)).trans (depth_eqProtocol_le n)
  omega

/-- **Equality of empty strings.** For zero-bit strings equality is the constant `true`,
computed with no communication, so its communication complexity is `0`. -/
theorem commComplexity_eqFn_zero : commComplexity (eqFn 0) = 0 := by
  refine Nat.eq_zero_of_le_zero (commComplexity_le_depth (p := output true) ?_)
  intro x y
  simp [eval, eqFn, Subsingleton.elim x y]

/-- **The log-rank conjecture (open).** There is a constant `C` such that every Boolean
function `f` on finite inputs has deterministic communication complexity at most
`C (log₂ rank M_f + 1) ^ C`, the rank taken over `ℝ` (L. Lovász and M. Saks, 1988; stated as
Conjecture 2.12 in A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, as
`D(M) ≤ log^α rank(M)`). The additive `+ 1` and the factor `C` make the statement meaningful
for matrices of rank one, which can need one bit. Stated as a proposition only; the lower
bound `⌈log₂ rank M_f⌉ ≤ D(f)` is `log_rank_le_commComplexity`. -/
def LogRankConjecture : Prop :=
  ∃ C : ℕ, ∀ (X Y : Type) [Finite X] [Fintype Y] (f : X → Y → Bool),
    (commComplexity f : ℝ) ≤ C * (Real.logb 2 (commMatrix ℝ f).rank + 1) ^ C

end MathlibExt.Computability.CommunicationComplexity
