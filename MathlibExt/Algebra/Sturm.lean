/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Algebra/Sturm.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `sturm` (manifest
`manifests/problems/sturm.toml`, rev 1, submitted by Kim Morrison).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"). You may obtain a copy at
https://www.apache.org/licenses/LICENSE-2.0. The adapted portions are distributed on an "AS IS"
basis, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License
for the specific language governing permissions and limitations. lean-eval ships no NOTICE file.

The adapted portions are `sturmAux`, `sturmChain`, `signChanges`, `sigma`, and the statement of
`sturm`. ATLAS placed these declarations in the namespace below, recorded the theorem as a wanted
statement, and subsequently moved the declarations to this module and supplied the proof.
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Sturm's theorem

For a squarefree real polynomial, `sturm` counts its distinct roots in an open interval
by the drop in sign variations of its signed remainder sequence. The proof shows that
each interior zero in the sequence leaves the variation locally constant, while a simple
root of the first polynomial contributes a drop of one.
-/

@[expose] public section

namespace MathlibExt.Algebra.SturmWanted.Algebra

open Polynomial

set_option linter.dupNamespace false in
open scoped Classical in
/-- **Negated-remainder sequence with fuel.** For real polynomials $a$, $b$ and a natural
number $n$, this is the list of polynomials defined recursively by: for $n = 0$ it is the
one-entry list $(a)$; for fuel $n + 1$ it is $(a)$ if $b = 0$, and otherwise it is $a$
followed by the list for the pair $b$, $-(a \bmod b)$ with fuel $n$, where $a \bmod b$ is the
remainder of $a$ on division by $b$. -/
noncomputable def sturmAux : ℝ[X] → ℝ[X] → ℕ → List ℝ[X]
  | a, _, 0       => [a]
  | a, b, (n + 1) =>
    if b = 0 then [a] else a :: sturmAux b (-(a % b)) n

set_option linter.dupNamespace false in
open scoped Classical in
/-- **Sturm chain.** The Sturm chain of a real polynomial $p$ is the list $p_0, p_1, \dots, p_m$
with $p_0 = p$, $p_1 = p'$ and $p_{k+1} = -(p_{k-1} \bmod p_k)$, the negated remainder of
$p_{k-1}$ on division by $p_k$, where the list stops at $p_m$ as soon as the next entry would
be $0$; thus $p_m$ is its last entry and, for $p \ne 0$, every entry is nonzero. For $p = 0$
the chain is the one-entry list $(0)$. -/
noncomputable def sturmChain (p : ℝ[X]) : List ℝ[X] :=
  sturmAux p (derivative p) (p.natDegree + 2)

set_option linter.dupNamespace false in
open scoped Classical in
/-- Number of sign changes in a list of real numbers, ignoring zeros: filter
the zeros out, then count adjacent pairs of opposite sign. -/
noncomputable def signChanges (xs : List ℝ) : ℕ :=
  let ys := xs.filter (· ≠ 0)
  ((ys.zip ys.tail).filter (fun q => q.1 * q.2 < 0)).length

set_option linter.dupNamespace false in
open scoped Classical in
/-- **Sturm sign-variation function.** For a real polynomial $p$ with Sturm chain
$p_0, p_1, \dots, p_m$ and a real number $x$, $\sigma_p(x)$ is the number of sign changes,
ignoring zeros, in the sequence of values $p_0(x), p_1(x), \dots, p_m(x)$. -/
noncomputable def sigma (p : ℝ[X]) (x : ℝ) : ℕ :=
  signChanges ((sturmChain p).map fun q => q.eval x)

open Filter Topology

-- With enough fuel the benchmark chain agrees with the Euclidean Sturm sequence.
private theorem aux_eq_sturmSeq (p q : ℝ[X]) (n : ℕ) (hp : p ≠ 0)
    (hn : q ≠ 0 → q.natDegree < n) : sturmAux p q n = sturmSeq p q := by
  induction n generalizing p q with
  | zero =>
    have hq : q = 0 := by simpa using hn
    simp [hq, sturmAux, hp]
  | succ n ih =>
    by_cases hq : q = 0
    · simp [hq, sturmAux, hp]
    rw [sturmAux, ite_eq_right hq, sturmSeq_cons hp, Polynomial.neg_mod]
    congr 1
    apply ih _ _ hq
    intro hr
    rw [natDegree_neg]
    exact (natDegree_lt_natDegree (neg_ne_zero.mp hr) (degree_mod_lt p hq)).trans_le
      (Nat.le_of_lt_succ (hn hq))

private theorem chain_eq_sturmSeq {p : ℝ[X]} (hp : p ≠ 0) :
    sturmChain p = sturmSeq p p.derivative := by
  apply aux_eq_sturmSeq _ _ _ hp
  have := natDegree_derivative_le p
  omega

-- When the second entry is nonzero, the first contributes exactly one adjacent pair.
private theorem changes_pair (u v : ℝ) (l : List ℝ) (hv : v ≠ 0) :
    signChanges (u :: v :: l) =
      (if u * v < 0 then 1 else 0) + signChanges (v :: l) := by
  by_cases hu : u = 0
  · simp [signChanges, hu]
  by_cases h : u * v < 0 <;> simp [signChanges, hu, hv, h, Nat.add_comm]

-- Opposite outer signs contribute one variation for every sign of the middle entry.
private theorem changes_triple (u v w : ℝ) (l : List ℝ) (h : u * w < 0) :
    signChanges (u :: v :: w :: l) = 1 + signChanges (w :: l) := by
  have hw : w ≠ 0 := by rintro rfl; simp at h
  by_cases hv : v = 0
  · subst v
    calc
      _ = signChanges (u :: w :: l) := by simp [signChanges, List.filter_cons]
      _ = _ := by simp [changes_pair u w l hw, h]
  rw [changes_pair u v _ hv, changes_pair v w _ hw]
  rcases mul_neg_iff.mp h with ⟨hu, hw'⟩ | ⟨hu, hw'⟩ <;>
    rcases lt_or_gt_of_ne hv with hv' | hv' <;>
    simp_all [mul_neg_iff, not_lt_of_gt]

private noncomputable abbrev variations (l : List ℝ[X]) (x : ℝ) : ℕ :=
  signChanges (l.map (fun q => q.eval x))

private theorem variations_pair (p q : ℝ[X]) (l : List ℝ[X]) {y : ℝ} (hq : q.eval y ≠ 0) :
    variations (p :: q :: l) y =
      (if p.eval y * q.eval y < 0 then 1 else 0) + variations (q :: l) y :=
  changes_pair _ _ _ hq

private theorem variations_triple (p q r : ℝ[X]) (l : List ℝ[X]) {y : ℝ}
    (h : p.eval y * r.eval y < 0) :
    variations (p :: q :: r :: l) y = 1 + variations (r :: l) y :=
  changes_triple _ _ _ _ h

private theorem eventually_neg_iff {f : ℝ → ℝ} {x : ℝ} (hf : ContinuousAt f x) (hx : f x ≠ 0) :
    ∀ᶠ y in 𝓝 x, f y < 0 ↔ f x < 0 := by
  rcases lt_or_gt_of_ne hx with h | h
  · exact (hf.eventually_lt continuousAt_const h).mono fun y hy => iff_of_true hy h
  · exact (continuousAt_const.eventually_lt hf h).mono fun y hy =>
      iff_of_false (not_lt_of_gt hy) (not_lt_of_gt h)

private theorem poly_ne_zero {p : ℝ[X]} {x : ℝ} (h : p.eval x ≠ 0) : p ≠ 0 := by
  rintro rfl
  simp at h

-- At a zero of the second polynomial, its neighbors have opposite signs throughout
-- a neighborhood. The first two entries then contribute a constant one variation.
private theorem variations_stable (p q : ℝ[X]) {x : ℝ} (hp : p.eval x ≠ 0) :
    ∀ᶠ y in 𝓝 x, variations (sturmSeq p q) y = variations (sturmSeq p q) x := by
  by_cases hq : q = 0
  · filter_upwards [p.continuousAt.eventually_ne hp] with y hy
    simp [hq, poly_ne_zero hp, variations, signChanges, hp, hy]
  let r := -p % q
  let s := -q % r
  have h₁ : sturmSeq p q = p :: sturmSeq q r := sturmSeq_cons (poly_ne_zero hp)
  have h₂ : sturmSeq q r = q :: sturmSeq r s := sturmSeq_cons hq
  by_cases hqx : q.eval x = 0
  · have hrx : r.eval x = -p.eval x := by
      simp [r, Polynomial.neg_mod, eval_mod_eq_self_of_root hqx]
    have hop : p.eval x * r.eval x < 0 := by simp [hrx, hp]
    have hr : r.eval x ≠ 0 := by simpa [hrx] using hp
    have h₃ := sturmSeq_cons (q := s) (poly_ne_zero hr)
    have ht := variations_stable r s hr
    filter_upwards [ht, (p.continuous.mul r.continuous).continuousAt.eventually_lt
      continuousAt_const hop] with y hy hyop
    rw [h₁, h₂, h₃, variations_triple _ _ _ _ hyop, variations_triple _ _ _ _ hop, ← h₃, hy]
  · have ht := variations_stable q r hqx
    filter_upwards [ht, q.continuousAt.eventually_ne hqx,
      eventually_neg_iff (p.continuous.mul q.continuous).continuousAt (mul_ne_zero hp hqx)]
      with y hy hqy hsign
    change p.eval y * q.eval y < 0 ↔ p.eval x * q.eval x < 0 at hsign
    rw [h₁, h₂, variations_pair _ _ _ hqy, variations_pair _ _ _ hqx, ← h₂, hy]
    simp only [hsign]
termination_by (sturmSeq p q).length
decreasing_by
  · change (sturmSeq r s).length < (sturmSeq p q).length
    simp [h₁, h₂]
  · change (sturmSeq q r).length < (sturmSeq p q).length
    simp [h₁]

-- At a simple root x, factor p as (X - C x) * q. The two factors q and p'
-- have the same nonzero value at x, so their product stays positive nearby.
private theorem eventually_root_crossing {p : ℝ[X]} {x : ℝ} (hx : p.eval x = 0)
    (hd : p.derivative.eval x ≠ 0) :
    ∀ᶠ y in 𝓝 x, p.eval y * p.derivative.eval y < 0 ↔ y < x := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hx
  have hdx : p.derivative.eval x = q.eval x := by simp [hq, derivative_mul]
  have hpos : 0 < q.eval x * p.derivative.eval x := by simp [← hdx, hd]
  filter_upwards [continuousAt_const.eventually_lt
    (q.continuous.mul p.derivative.continuous).continuousAt hpos] with y hy
  change 0 < q.eval y * p.derivative.eval y at hy
  rw [show p.eval y = (y - x) * q.eval y by simp [hq]]
  simp [mul_assoc, mul_neg_iff, hy, not_lt_of_gt hy]

private theorem sigma_near_root {p : ℝ[X]} {x : ℝ} (hx : p.eval x = 0)
    (hp : p ≠ 0) (hd : p.derivative.eval x ≠ 0) :
    ∀ᶠ y in 𝓝 x, sigma p y = (if y < x then 1 else 0) + sigma p x := by
  let r := -p % p.derivative
  have h₁ : sturmChain p = p :: sturmSeq p.derivative r :=
    (chain_eq_sturmSeq hp).trans (sturmSeq_cons hp)
  have h₂ := sturmSeq_cons (q := r) (poly_ne_zero hd)
  filter_upwards [variations_stable p.derivative r hd,
    p.derivative.continuousAt.eventually_ne hd, eventually_root_crossing hx hd]
    with y hy hdy hcross
  change variations (sturmChain p) y = _ + variations (sturmChain p) x
  rw [h₁, h₂, variations_pair _ _ _ hdy, variations_pair _ _ _ hd, ← h₂, hy]
  simp [hx, hcross]

private theorem eventually_filter_le (s : Finset ℝ) {x : ℝ} (hx : x ∉ s) :
    ∀ᶠ y in 𝓝 x, s.filter (· ≤ y) = s.filter (· ≤ x) := by
  have h : ∀ r ∈ s, ∀ᶠ y in 𝓝 x, r ≤ y ↔ r ≤ x := by
    intro r hr
    rcases lt_or_gt_of_ne (ne_of_mem_of_not_mem hr hx) with h | h
    · exact (lt_mem_nhds h).mono fun y hy => iff_of_true (le_of_lt hy) h.le
    · exact (gt_mem_nhds h).mono fun y hy => iff_of_false (not_le_of_gt hy) h.not_ge
  exact (s.eventually_all.mpr h).mono fun _ hy => Finset.filter_congr hy

-- The roots counted through x compensate exactly for the jumps in the variation.
private theorem locallyConstant_total {p : ℝ[X]} (hp : Squarefree p) :
    IsLocallyConstant fun x => sigma p x + (p.roots.toFinset.filter (· ≤ x)).card := by
  let roots := p.roots.toFinset
  have hroot (x : ℝ) : x ∈ roots ↔ p.eval x = 0 :=
    Multiset.mem_toFinset.trans (mem_roots hp.ne_zero)
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  change ∀ᶠ y in 𝓝 x, sigma p y + (roots.filter (· ≤ y)).card =
    sigma p x + (roots.filter (· ≤ x)).card
  by_cases hx : x ∈ roots
  · have hev := (hroot x).mp hx
    have hsep := PerfectField.separable_iff_squarefree.mpr hp
    have hd : p.derivative.eval x ≠ 0 := hsep.eval₂_derivative_ne_zero (RingHom.id ℝ) hev
    have hcard (y : ℝ) : (roots.filter (· ≤ y)).card =
        (if x ≤ y then 1 else 0) + ((roots.erase x).filter (· ≤ y)).card := by
      conv_lhs => rw [← Finset.insert_erase hx, Finset.filter_insert]
      by_cases hxy : x ≤ y <;> simp [hxy, Nat.add_comm]
    filter_upwards [sigma_near_root hev hp.ne_zero hd,
      eventually_filter_le (roots.erase x) (Finset.notMem_erase x roots)] with y hy hfix
    rw [hy, hcard y, hcard x, hfix]
    rcases lt_or_ge y x with h | h
    · simp [h, h.not_ge, Nat.add_assoc, Nat.add_left_comm]
    · simp [h, h.not_gt]
  · have hfix := variations_stable p p.derivative (fun h => hx ((hroot x).mpr h))
    filter_upwards [hfix, eventually_filter_le roots hx] with y hy heq
    simpa only [sigma, chain_eq_sturmSeq hp.ne_zero, heq] using congrArg
      (· + (roots.filter (· ≤ x)).card) hy

set_option linter.dupNamespace false in
open scoped Classical in
/-- **Sturm's theorem.** Let $p$ be a squarefree real polynomial and let $a < b$ be real numbers
with $p(a) \ne 0$ and $p(b) \ne 0$. Then the number of distinct real roots $x$ of $p$ with
$a < x < b$ equals $\sigma_p(a) - \sigma_p(b)$, where $\sigma_p$ is the Sturm sign-variation
function of $p$ and the subtraction is truncated subtraction of natural numbers.

Source: J. C. F. Sturm (1829). Listed as §97 in O. Knill, Some Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Formalized in
Isabelle/HOL by Manuel Eberl (AFP entry Sturm_Sequences). Via leanprover/lean-eval@38361be, problem
`sturm`. -/
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  let roots := p.roots.toFinset
  have htotal := (locallyConstant_total hp).apply_eq_of_preconnectedSpace a b
  change sigma p a + (roots.filter (· ≤ a)).card =
    sigma p b + (roots.filter (· ≤ b)).card at htotal
  have hpartition := (roots.filter (· ≤ b)).card_filter_add_card_filter_not (· ≤ a)
  have hleft : (roots.filter (· ≤ b)).filter (· ≤ a) = roots.filter (· ≤ a) := by
    ext x
    simp only [Finset.mem_filter]
    grind
  have hright : (roots.filter (· ≤ b)).filter (fun x => ¬ x ≤ a) =
      roots.filter (fun x => a < x ∧ x < b) := by
    have hb' : b ∉ roots := fun h =>
      hb ((mem_roots (poly_ne_zero ha)).mp (Multiset.mem_toFinset.mp h))
    ext x
    simp only [Finset.mem_filter]
    grind
  rw [hleft, hright] at hpartition
  change (roots.filter _).card = _
  omega

end MathlibExt.Algebra.SturmWanted.Algebra
