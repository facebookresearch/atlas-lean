/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Crypto.Protocols.SecretSharing.Shamir
public import Mathlib.LinearAlgebra.Lagrange

/-!
# BGW share algebra: product degree and recombination

Share-level facts for the multiplication step of BGW-style protocols: multiplying
two degree-`t` sharings yields a degree-`2 * t` sharing of the product secret,
which the full party set can recombine when `2 * t` is below the number of
parties.

## Setting

`F` is a field and `x : Party → F` assigns each party a distinct nonzero
evaluation point. A degree-`t` sharing of a secret `s` is the family of
evaluations of a polynomial `p` with `p.natDegree ≤ t` and `p.eval 0 = s`.

## Main results

- `natDegree_mul_le_two_mul` (B1): the product polynomial has degree at most
  `2 * t`.
- `exists_recombination_vector` (B2): when `2 * t < n`, Lagrange interpolation
  at `0` gives a recombination vector recovering `p.eval 0` from all `n`
  shares, uniformly in `p`.
- `exists_ambiguous_sharings` (B3): when `n ≤ 2 * t`, two degree-`2 * t`
  sharings can agree on every share yet differ in the secret.
- `no_recombination_vector_of_le` (B3): hence no recombination vector exists
  when `n ≤ 2 * t`.
- `shamir_authorized_iff` (B4): with Shamir parameters of threshold `t`, a
  coalition is authorized iff it holds more than `t` shares.
- `shamir_exists_recombination_vector` (B4): B2 restated over Shamir
  parameters.

Reconstruction needs `t + 1` shares while at most `t` corruptions are
tolerated; the two thresholds are kept distinct throughout. Re-sharing the
product with fresh randomness (degree reduction proper) is out of scope here.

## References

* [M. Ben-Or, S. Goldwasser, A. Wigderson,
  *Completeness theorems for non-cryptographic fault-tolerant distributed
  computation* (extended abstract), Proc. 20th Annual ACM Symp. on Theory of
  Computing (STOC), Chicago, May 1988, pp. 1–10, ACM][BGW1988],
  DOI `10.1145/62212.62213`. Section and page numbers below were verified
  against the copy at `https://mit6875.github.io/PAPERS/BGW.pdf` (10 pages;
  printed page numbers match the proceedings pagination; ACM line
  `0-89791-264-0/88/0005/0001` on p. 1).

Claim correspondence (all locators in [BGW1988], proof of Theorem 1):
`natDegree_mul_le_two_mul` (B1) is the degree fact behind "The multiplication
step" (p. 4): for `h = f * g` the paper notes the degree "is `2t` instead of
`t`". The local-share equation `Si = h(αi) = f(αi) * g(αi)` and the fixed
linear recombination `R = S * A` (with `A = B⁻¹PB` for the Vandermonde matrix
`B`) are in "The degree reduction step" (p. 4), building on the Lemma (Linear
Functional, p. 3) and the Corollary (Matrix Multiplication, p. 4).
`exists_recombination_vector` (B2) formalizes this interpolation step as a
Lagrange-at-`0` recombination vector, which exists exactly when `2 * t < n`,
i.e. the proof's standing hypothesis `n ≥ 2 * t + 1` (p. 3); the boundary
results (`exists_ambiguous_sharings`, `no_recombination_vector_of_le`, B3)
are its converse. Threshold convention: `t` is the corruption bound
(Theorem 1, `t < n / 2`, Abstract on p. 1, restated p. 4); reconstruction
needs `t + 1` shares for a degree-`t` sharing ("The input stage" and "The
final stage", p. 3) and `2 * t + 1` for the degree-`2 * t` product. Full
re-sharing with fresh randomness ("The randomization step", p. 4) and the
`t < n / 3` Byzantine case (Theorems 3–4, stated p. 3) are out of scope here.
-/

@[expose] public section

namespace CSLibExt.Crypto.Protocols.BGW

/-- Product of two degree-`t` sharings has degree at most `2 * t`.
`Polynomial.natDegree_mul_le` holds unconditionally, so the zero-polynomial
edge case (`natDegree 0 = 0`) needs no special casing. -/
theorem natDegree_mul_le_two_mul
    {F : Type*} [Field F] (p q : _root_.Polynomial F) (t : ℕ)
    (hp : p.natDegree ≤ t) (hq : q.natDegree ≤ t) :
    (p * q).natDegree ≤ 2 * t := by
  calc (p * q).natDegree
      ≤ p.natDegree + q.natDegree := _root_.Polynomial.natDegree_mul_le
    _ ≤ t + t := Nat.add_le_add hp hq
    _ = 2 * t := (two_mul t).symm

/-- Recombination vector for degree-`2 * t` sharings (BGW multiplication step).

If `2 * t < n` where `n` is the number of parties, there is a vector `r`,
independent of `p`, recovering `p.eval 0` from the `n` point evaluations. The
vector is Lagrange interpolation at `0` on the `n` evaluation points. -/
theorem exists_recombination_vector
    {F Party : Type*} [Field F] [Fintype Party]
    (x : Party → F) (hx_inj : Function.Injective x) (t : ℕ)
    (hcard : 2 * t < Fintype.card Party) :
    ∃ r : Party → F, ∀ p : _root_.Polynomial F, p.natDegree ≤ 2 * t →
      p.eval 0 = ∑ i, r i * p.eval (x i) := by
  classical
  refine ⟨fun i => (_root_.Lagrange.basis Finset.univ x i).eval 0, fun p hp => ?_⟩
  show p.eval 0 = ∑ i, (_root_.Lagrange.basis Finset.univ x i).eval 0 * p.eval (x i)
  have hvs : Set.InjOn x (Finset.univ : Finset Party) := hx_inj.injOn
  have hlt : p.natDegree < (Finset.univ : Finset Party).card := by
    rw [Finset.card_univ]
    exact lt_of_le_of_lt hp hcard
  have hdeg : p.degree < ((Finset.univ : Finset Party).card : WithBot ℕ) := by
    by_cases hp0 : p = 0
    · subst hp0
      rw [_root_.Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · rw [_root_.Polynomial.degree_eq_natDegree hp0]
      exact_mod_cast hlt
  have heq := _root_.Lagrange.eq_interpolate (s := Finset.univ) (v := x) hvs hdeg
  conv_lhs => rw [heq]
  rw [_root_.Lagrange.interpolate_apply, _root_.Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_C]
  exact mul_comm _ _

/-- Boundary: with `n ≤ 2 * t` points, point evaluations do not determine the
secret. The vanishing polynomial `∏ i, (X - C (x i))` agrees with `0` on every
point but is nonzero at `0` since no point is `0`. -/
theorem exists_ambiguous_sharings
    {F Party : Type*} [Field F] [Fintype Party]
    (x : Party → F) (hx_ne : ∀ i, x i ≠ 0) (t : ℕ)
    (hcard : Fintype.card Party ≤ 2 * t) :
    ∃ p q : _root_.Polynomial F,
      p.natDegree ≤ 2 * t ∧ q.natDegree ≤ 2 * t ∧
        (∀ i, p.eval (x i) = q.eval (x i)) ∧ p.eval 0 ≠ q.eval 0 := by
  classical
  refine ⟨∏ i ∈ Finset.univ, (_root_.Polynomial.X - _root_.Polynomial.C (x i)),
    0, ?_, ?_, ?_, ?_⟩
  · have hne : ∀ i ∈ Finset.univ,
        _root_.Polynomial.X - _root_.Polynomial.C (x i) ≠ 0 :=
        fun i _ => _root_.Polynomial.X_sub_C_ne_zero (x i)
    have h1 : ∀ i ∈ Finset.univ,
        (_root_.Polynomial.X - _root_.Polynomial.C (x i)).natDegree = 1 :=
        fun i _ => _root_.Polynomial.natDegree_X_sub_C (x i)
    calc (∏ i ∈ Finset.univ,
            (_root_.Polynomial.X - _root_.Polynomial.C (x i))).natDegree
        = ∑ i ∈ Finset.univ,
            (_root_.Polynomial.X - _root_.Polynomial.C (x i)).natDegree :=
          _root_.Polynomial.natDegree_prod _ _ hne
      _ = ∑ i ∈ Finset.univ, 1 := Finset.sum_congr rfl h1
      _ = Fintype.card Party := by simp
      _ ≤ 2 * t := hcard
  · rw [_root_.Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · intro i
    rw [_root_.Polynomial.eval_prod, _root_.Polynomial.eval_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [_root_.Polynomial.eval_sub]
  · rw [_root_.Polynomial.eval_prod, _root_.Polynomial.eval_zero]
    rw [Finset.prod_ne_zero_iff]
    intro i _
    simp only [_root_.Polynomial.eval_sub, _root_.Polynomial.eval_X,
      _root_.Polynomial.eval_C, zero_sub, neg_ne_zero]
    exact hx_ne i

/-- Corollary: no recombination vector exists when `n ≤ 2 * t`. Any candidate
vector gives the same output on the two ambiguous sharings above, although
their secrets differ. -/
theorem no_recombination_vector_of_le
    {F Party : Type*} [Field F] [Fintype Party]
    (x : Party → F) (hx_ne : ∀ i, x i ≠ 0) (t : ℕ)
    (hcard : Fintype.card Party ≤ 2 * t) :
    ¬ ∃ r : Party → F, ∀ p : _root_.Polynomial F, p.natDegree ≤ 2 * t →
      p.eval 0 = ∑ i, r i * p.eval (x i) := by
  rintro ⟨r, hr⟩
  obtain ⟨p, q, hple, hqle, hagree, hne⟩ :=
    exists_ambiguous_sharings x hx_ne t hcard
  have hsum : (∑ i, r i * p.eval (x i)) = ∑ i, r i * q.eval (x i) :=
    Finset.sum_congr rfl fun i _ => by rw [hagree i]
  have hp := hr p hple
  have hq := hr q hqle
  apply hne
  rw [hp, hq, hsum]

/-- With Shamir parameters of threshold `t`, a coalition is authorized iff it
holds more than `t` shares: reconstruction needs `t + 1` shares while the
corruption bound is `t` (coalitions of size at most `t` are unauthorized). -/
theorem shamir_authorized_iff
    {F Party : Type*} [Field F] [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (s : Finset Party) :
    Cslib.Crypto.Protocols.SecretSharing.Shamir.authorized params s ↔
      params.threshold < s.card := by
  unfold Cslib.Crypto.Protocols.SecretSharing.Shamir.authorized
  exact Nat.succ_le_iff

/-- The B2 recombination vector restated for Shamir parameters: with
`n = Fintype.card Party` parties and corruption bound `t = params.threshold`,
`2 * t < n` yields a recombination vector over `params.point`. -/
theorem shamir_exists_recombination_vector
    {F Party : Type*} [Field F] [Fintype Party]
    (params : Cslib.Crypto.Protocols.SecretSharing.Shamir.Params F Party)
    (hcard : 2 * params.threshold < Fintype.card Party) :
    ∃ r : Party → F, ∀ p : _root_.Polynomial F,
      p.natDegree ≤ 2 * params.threshold →
        p.eval 0 = ∑ i, r i * p.eval (params.point i) :=
  exists_recombination_vector params.point params.point_injective
    params.threshold hcard

end CSLibExt.Crypto.Protocols.BGW
