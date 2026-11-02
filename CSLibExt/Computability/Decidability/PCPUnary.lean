/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PCP over a one-letter alphabet is decidable
-/
module

public import CSLibExt.Computability.Decidability.PCP
public import Mathlib.Tactic.Ring

/-!
# PCP over a one-letter alphabet is decidable

Over an alphabet with at most one letter a word is determined by its length. So `P` has a PCP
solution iff some domino is balanced (top and bottom of equal length), or some domino is
short on top and some other domino is short on the bottom. In the second case, if `d` has
deficit `δ` on top and `e` has surplus `ε`, then `ε` copies of `d` followed by `δ` copies of
`e` balance. Otherwise every domino is longer on the same side, and so is every nonempty
sequence of them. The criterion is a primitive recursive test on `P`, so the problem is
decidable, by a `FinTM2` in particular.

## Main results

- `pcp_iff_of_subsingleton` : the length criterion.
- `computablePred_pcp_of_subsingleton`, `tm2Decidable_pcp_of_subsingleton` : decidability.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013,
  Exercise 5.24 (PCP over a unary alphabet is decidable).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability.Post

variable {α : Type*}

theorem length_top (s : List (Domino α)) : (top s).length = (s.map fun d ↦ d.1.length).sum :=
  List.length_flatMap

theorem length_bottom (s : List (Domino α)) :
    (bottom s).length = (s.map fun d ↦ d.2.length).sum :=
  List.length_flatMap

/-- **Total length of dominoes that are at least as long on top.** Write $|w|$ for the length of a
word $w$. Let $s$ be a finite sequence of dominoes over an alphabet. If every domino $(t, b)$ in
$s$ satisfies $|b| \le |t|$, then the concatenation of the bottom words of $s$ is no longer than
the concatenation of the top words of $s$. -/
theorem length_bottom_le_length_top {s : List (Domino α)}
    (h : ∀ d ∈ s, d.2.length ≤ d.1.length) : (bottom s).length ≤ (top s).length := by
  induction s with
  | nil => simp
  | cons d s ih =>
    simp only [bottom_cons, top_cons, List.length_append]
    have := h d List.mem_cons_self
    have := ih fun e he ↦ h e (List.mem_cons_of_mem _ he)
    omega

/-- **Total length of dominoes that are strictly longer on top.** Write $|w|$ for the length of a
word $w$. Let $s$ be a nonempty finite sequence of dominoes over an alphabet. If every domino
$(t, b)$ in $s$ satisfies $|b| < |t|$, then the concatenation of the bottom words of $s$ is strictly
shorter than the concatenation of the top words of $s$. -/
theorem length_bottom_lt_length_top {s : List (Domino α)} (hs : s ≠ [])
    (h : ∀ d ∈ s, d.2.length < d.1.length) : (bottom s).length < (top s).length := by
  obtain ⟨d, s, rfl⟩ := List.exists_cons_of_ne_nil hs
  simp only [bottom_cons, top_cons, List.length_append]
  have := h d List.mem_cons_self
  have := length_bottom_le_length_top (s := s) fun e he ↦
    (h e (List.mem_cons_of_mem _ he)).le
  omega

/-- **Swapping top and bottom.** For a finite sequence $s$ of dominoes, the swapped sequence is
obtained from $s$ by exchanging the top and bottom word of every domino: each $(t, b)$ becomes
$(b, t)$, and the order of the dominoes is unchanged. -/
def swap (s : List (Domino α)) : List (Domino α) := s.map Prod.swap

@[simp] theorem top_swap (s : List (Domino α)) : top (swap s) = bottom s := by
  induction s with
  | nil => rfl
  | cons d s ih => exact congrArg (d.2 ++ ·) ih

@[simp] theorem bottom_swap (s : List (Domino α)) : bottom (swap s) = top s := by
  induction s with
  | nil => rfl
  | cons d s ih => exact congrArg (d.1 ++ ·) ih

theorem top_replicate (n : ℕ) (d : Domino α) :
    (top (List.replicate n d)).length = n * d.1.length := by
  rw [length_top, List.map_replicate, List.sum_replicate, smul_eq_mul]

theorem bottom_replicate (n : ℕ) (d : Domino α) :
    (bottom (List.replicate n d)).length = n * d.2.length := by
  rw [length_bottom, List.map_replicate, List.sum_replicate, smul_eq_mul]

private theorem primrec_list_any [Primcodable α] {p : Domino α → Bool} (hp : Primrec p) :
    Primrec fun P : List (Domino α) ↦ P.any p := by
  refine (Primrec.list_foldr Primrec.id (Primrec.const false)
    (Primrec.or.comp (hp.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun P ↦ ?_
  simp only [id]
  induction P with
  | nil => rfl
  | cons d P ih => simp only [List.foldr_cons, List.any_cons, ih]

variable [Subsingleton α]

theorem eq_of_length_eq {u v : List α} (h : u.length = v.length) : u = v :=
  List.ext_getElem h fun _ _ _ ↦ Subsingleton.elim _ _

/-- **The unary PCP criterion.** Let $\alpha$ be an alphabet with at most one letter, and write
$|w|$ for the length of a word $w$. A finite list $P$ of dominoes over $\alpha$ has a PCP solution
if and only if either some domino $(t, b)$ in $P$ has $|t| = |b|$, or some domino $(t, b)$ in $P$
has $|t| < |b|$ and some domino $(t', b')$ in $P$ has $|b'| < |t'|$. -/
theorem pcp_iff_of_subsingleton (P : List (Domino α)) :
    PCP P ↔ (∃ d ∈ P, d.1.length = d.2.length) ∨
      ((∃ d ∈ P, d.1.length < d.2.length) ∧ ∃ e ∈ P, e.2.length < e.1.length) := by
  constructor
  · rintro ⟨s, hne, hmem, heq⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hbal, hmix⟩ := hcon
    have hlen := congrArg List.length heq
    by_cases hshort : ∃ d ∈ P, d.1.length < d.2.length
    · -- every domino is short on top
      have hall : ∀ d ∈ swap s, d.2.length < d.1.length := by
        intro d hd
        obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
        have h₁ := hbal d' (hmem d' hd')
        have h₂ := hmix hshort d' (hmem d' hd')
        simp only [Prod.fst_swap, Prod.snd_swap]
        omega
      have := length_bottom_lt_length_top (by simpa [swap] using hne) hall
      simp only [bottom_swap, top_swap] at this
      omega
    · push Not at hshort
      have hall : ∀ d ∈ s, d.2.length < d.1.length := by
        intro d hd
        have h₁ := hbal d (hmem d hd)
        have h₂ := hshort d (hmem d hd)
        omega
      have := length_bottom_lt_length_top hne hall
      omega
  · rintro (⟨d, hd, hbal⟩ | ⟨⟨d, hd, hdlt⟩, ⟨e, he, helt⟩⟩)
    · exact ⟨[d], List.cons_ne_nil _ _, by simpa using hd, eq_of_length_eq (by simpa using hbal)⟩
    · refine ⟨List.replicate (e.1.length - e.2.length) d ++
        List.replicate (d.2.length - d.1.length) e, ?_, ?_, ?_⟩
      · simp only [ne_eq, List.append_eq_nil_iff, List.replicate_eq_nil_iff, not_and]
        omega
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx <;>
          obtain ⟨-, rfl⟩ := List.mem_replicate.mp hx <;> assumption
      · apply eq_of_length_eq
        rw [top_append, bottom_append, List.length_append, List.length_append, top_replicate,
          top_replicate, bottom_replicate, bottom_replicate]
        obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_lt helt
        obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_lt hdlt
        rw [ha, hb, show e.2.length + a + 1 - e.2.length = a + 1 by omega,
          show d.1.length + b + 1 - d.1.length = b + 1 by omega]
        ring

/-! ### Decidability -/

/-- **The unary PCP test.** Let $\alpha$ be an alphabet with at most one letter, and write $|w|$
for the length of a word $w$. For a finite list $P$ of dominoes over $\alpha$, the unary test of
$P$ is the Boolean value that is true exactly when some domino $(t, b)$ in $P$ has $|t| = |b|$, or
some domino $(t, b)$ in $P$ has $|t| < |b|$ and some domino $(t', b')$ in $P$ has $|b'| < |t'|$. -/
def unaryTest (P : List (Domino α)) : Bool :=
  P.any (fun d ↦ d.1.length == d.2.length) ||
    (P.any (fun d ↦ decide (d.1.length < d.2.length)) &&
      P.any fun e ↦ decide (e.2.length < e.1.length))

theorem unaryTest_iff (P : List (Domino α)) : unaryTest P = true ↔ PCP P := by
  rw [pcp_iff_of_subsingleton]
  simp [unaryTest]

variable [Primcodable α]

/-- **PCP over a one-letter alphabet is decidable.** Let $\alpha$ be an alphabet with at most one
letter whose elements have a computable encoding. Then the Post correspondence problem over
$\alpha$ is a computable predicate: some computable function decides, for every finite list $P$
of dominoes over $\alpha$, whether $P$ has a PCP solution. -/
theorem computablePred_pcp_of_subsingleton : ComputablePred (PCP (α := α)) := by
  refine ComputablePred.computable_iff.mpr ⟨unaryTest, ?_, ?_⟩
  · have h1 : Primrec fun d : Domino α ↦ d.1.length == d.2.length :=
      Primrec.beq.comp (Primrec.list_length.comp Primrec.fst)
        (Primrec.list_length.comp Primrec.snd)
    have h2 : Primrec fun d : Domino α ↦ decide (d.1.length < d.2.length) :=
      (Primrec.nat_lt.comp (Primrec.list_length.comp Primrec.fst)
        (Primrec.list_length.comp Primrec.snd)).decide
    have h3 : Primrec fun d : Domino α ↦ decide (d.2.length < d.1.length) :=
      (Primrec.nat_lt.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.list_length.comp Primrec.fst)).decide
    exact (Primrec.or.comp (primrec_list_any h1)
      (Primrec.and.comp (primrec_list_any h2)
        (primrec_list_any h3))).to_comp
  · funext P
    exact propext (unaryTest_iff P).symm

/-- **Unary PCP is decidable by a multi-stack machine.** Let $\alpha$ be an alphabet with at most
one letter whose elements have a computable encoding. Then the Post correspondence problem over
$\alpha$ is decidable by a multi-stack machine: some multi-stack Turing machine decides, for every
finite list $P$ of dominoes over $\alpha$, whether $P$ has a PCP solution. -/
theorem tm2Decidable_pcp_of_subsingleton : TM2Decidable (PCP (α := α)) :=
  tm2Decidable_iff_computablePred.mpr computablePred_pcp_of_subsingleton

end Cslib.Decidability.Post
