/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Roots

/-!
# One-variable Boolean sum-check

The sum-check protocol of Lund, Fortnow, Karloff and Nisan lets a prover convince a verifier
that a polynomial over a finite field `F` sums to a claimed value `H` over the Boolean cube.
This file treats the one-variable case: the claim is `p.eval 0 + p.eval 1 = H` for a
polynomial `p` of degree at most `d`, which the verifier can evaluate once (oracle access).
The prover sends a polynomial `q`, purportedly `p`. The verifier accepts at challenge `r`
(drawn uniformly from `F` in the protocol) when

* `q.natDegree ≤ d` (the degree bound is checked, not assumed),
* `q.eval 0 + q.eval 1 = H`, and
* `q.eval r = p.eval r`.

The degree check is what makes the protocol sound: without it, over `ZMod 5` the message
`1 - X ^ 4` passes the other two checks for the false claim `p = 0`, `H = 1` at all four
nonzero challenges.

## Main results

* `accept1`: the verifier's acceptance predicate.
* `sumcheck1_complete`: for a true claim, the honest prover `q = p` is accepted at every
  challenge.
* `sumcheck1_sound`: for a false claim, every prover message is accepted at no more than `d`
  of the `|F|` challenges, so with probability at most `d / |F|`.
* `card_agree_le`: two distinct polynomials of degree at most `d` agree at no more than `d`
  points, the root bound behind soundness.

## References

* C. Lund, L. Fortnow, H. Karloff and N. Nisan, "Algebraic methods for interactive proof
  systems", Journal of the ACM 39(4) (1992), 859–868.
-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] public section

open Polynomial

namespace MathlibExt.Complexity.SumCheck

/-- One-variable Boolean sum-check verifier with degree bound `d`: for the claim
"`p.eval 0 + p.eval 1 = H`", it accepts the prover's polynomial `q` at challenge `r` when
`q` has degree at most `d`, the Boolean sum of `q` is `H`, and `q` agrees with the oracle
`p` at `r`. -/
def accept1 (d : ℕ) (p q : F[X]) (H r : F) : Prop :=
  q.natDegree ≤ d ∧ q.eval 0 + q.eval 1 = H ∧ q.eval r = p.eval r

instance (d : ℕ) (p q : F[X]) (H r : F) : Decidable (accept1 d p q H r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

omit [Fintype F] [DecidableEq F] in
/-- Completeness: if `p` has degree at most `d` and the claim is true, the honest prover
`q = p` is accepted at every challenge. -/
theorem sumcheck1_complete {d : ℕ} {p : F[X]} (hp : p.natDegree ≤ d) {H : F}
    (hH : p.eval 0 + p.eval 1 = H) (r : F) : accept1 d p p H r :=
  ⟨hp, hH, rfl⟩

/-- Root bound: a polynomial `q` different from `p`, both of degree at most `d`, agrees with
`p` at no more than `d` points. -/
theorem card_agree_le (p q : F[X]) (d : ℕ)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (hne : q ≠ p) :
    (Finset.univ.filter (fun r => q.eval r = p.eval r)).card
      ≤ d := by
  have hsub : q - p ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (q - p).natDegree ≤ d :=
    le_trans (natDegree_sub_le q p) (max_le hq hp)
  have hsub2 : (Finset.univ.filter (fun r => q.eval r = p.eval r)).card
      ≤ (q - p).natDegree := by
    apply card_le_degree_of_subset_roots
    intro a ha
    simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [mem_roots hsub, IsRoot.def]
    rw [eval_sub, sub_eq_zero]
    exact ha
  exact le_trans hsub2 hdeg

/-- Soundness: if `p` has degree at most `d` and the claim is false
(`H ≠ p.eval 0 + p.eval 1`), then every prover message `q` is accepted at no more than `d`
challenges. A message failing the degree or Boolean-sum check is accepted nowhere; one
passing both differs from `p`, so `card_agree_le` applies. -/
theorem sumcheck1_sound {d : ℕ} {p : F[X]} (hp : p.natDegree ≤ d) {H : F}
    (hH : H ≠ p.eval 0 + p.eval 1) (q : F[X]) :
    (Finset.univ.filter (fun r => accept1 d p q H r)).card ≤ d := by
  by_cases hq : q.natDegree ≤ d ∧ q.eval 0 + q.eval 1 = H
  · obtain ⟨hqd, hqH⟩ := hq
    have hne : q ≠ p := by
      rintro rfl
      exact hH hqH.symm
    refine le_trans (Finset.card_le_card fun r hr => ?_) (card_agree_le p q d hp hqd hne)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact hr.2.2
  · have hempty : Finset.univ.filter (fun r => accept1 d p q H r) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun r _ hr => hq ⟨hr.1, hr.2.1⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le d

end MathlibExt.Complexity.SumCheck
