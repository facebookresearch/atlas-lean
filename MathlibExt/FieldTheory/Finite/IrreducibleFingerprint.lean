/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot

/-!
# Fingerprinting by random irreducible polynomials: the counting bound

Rabin (*Fingerprinting by random polynomials*, Harvard Aiken Computation Laboratory TR-15-81,
1981) fingerprints a bit string `x₁ … xₙ` by the residue of `a(t) = x₁ t^(n-1) + ⋯ + xₙ` modulo a
randomly chosen irreducible polynomial `p(t)` of degree `k` over `ℤ₂`. A fingerprint collision
`a ≡ b (mod p)` with `a ≠ b` means `p ∣ a - b`. The error analysis of his Theorem 3 rests on one
counting fact (his equation (6)): a nonzero polynomial `H` has at most `deg H / k` distinct monic
irreducible factors of degree `k`, because their product divides `H`.

* `card_filter_dvd_mul_le_natDegree`: for any finite set `S` of monic irreducible polynomials of
  degree `k` over a field, `#{f ∈ S | f ∣ H} · k ≤ deg H` for `H ≠ 0`.
* `card_filter_exists_dvd_mul_le_sum_natDegree`: the same for the polynomials dividing some
  nonzero member of a finite family `g i`, with `∑ deg (g i)` on the right. With `g i = a - aᵢ`
  (pattern against the `i`-th text window, `deg ≤ n`) this is Rabin's
  `ℓ k = deg P ≤ deg H ≤ n m` for the number `ℓ` of irreducible `p` that produce an error.

Dividing by the number of monic irreducible polynomials of degree `k` gives the error
probability of Theorem 3. For prime `k` that number is `(2^k - 2)/k` over `ℤ₂` (Rabin's Lemma 1,
`ncard_monic_irreducible_zmod_two_of_prime`), and `(p^k - p)/k` over `ℤ/pℤ`
(`ncard_monic_irreducible_mul_of_prime`). The proof is Rabin's: every `α ∈ GF(p^k) ∖ 𝔽_p` has a
minimal polynomial of degree dividing `k`, hence equal to `k`; every monic irreducible `f` of
degree `k` has a root in `GF(p^k)` (since `𝔽_p[X]/(f)` has `p^k` elements, it is isomorphic to
`GF(p^k)`); and the roots of `f` there are `k` distinct elements, all with minimal polynomial `f`.

The counting bounds hold over every field and every degree `k`, and the irreducible count over
every prime field, which is more general than the source's `ℤ₂`.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt.Fingerprint

open Polynomial

variable {K : Type*} [Field K]

/-- Distinct monic irreducible polynomials are coprime. -/
private theorem isCoprime_of_monic_irreducible {f g : K[X]} (hf : f.Monic) (hg : g.Monic)
    (hfi : Irreducible f) (hgi : Irreducible g) (hfg : f ≠ g) : IsCoprime f g := by
  rw [hfi.coprime_iff_not_dvd]
  intro hdvd
  exact hfg (eq_of_monic_of_associated hf hg (hfi.associated_of_dvd hgi hdvd))

open Classical in
/-- **At most `deg H / k` irreducible factors of degree `k`.** Let `S` be a finite set of monic
irreducible polynomials of degree `k` over a field and `H ≠ 0`. The members of `S` that divide `H`
number at most `deg H / k`, in the form `#{f ∈ S | f ∣ H} · k ≤ deg H`: their product divides `H`
(Rabin, *Fingerprinting by random polynomials*, TR-15-81, 1981, proof of Theorem 3,
equation (6)). -/
theorem card_filter_dvd_mul_le_natDegree (S : Finset K[X]) (k : ℕ)
    (hS : ∀ f ∈ S, f.Monic ∧ Irreducible f ∧ f.natDegree = k) {H : K[X]} (hH : H ≠ 0) :
    (S.filter (· ∣ H)).card * k ≤ H.natDegree := by
  set T := S.filter (· ∣ H) with hT
  have hTS : ∀ f ∈ T, f.Monic ∧ Irreducible f ∧ f.natDegree = k := fun f hf =>
    hS f (Finset.mem_filter.1 hf).1
  have hprod : (∏ f ∈ T, f) ∣ H := by
    refine Finset.prod_dvd_of_coprime ?_ fun f hf => (Finset.mem_filter.1 hf).2
    intro f hf g hg hfg
    exact isCoprime_of_monic_irreducible (hTS f hf).1 (hTS g hg).1 (hTS f hf).2.1
      (hTS g hg).2.1 hfg
  have hdeg : (∏ f ∈ T, f).natDegree = T.card * k := by
    rw [natDegree_prod_of_monic T (fun f => f) fun f hf => (hTS f hf).1]
    rw [Finset.sum_congr rfl fun f hf => (hTS f hf).2.2, Finset.sum_const, smul_eq_mul]
  rw [← hdeg]
  exact natDegree_le_of_dvd hprod hH

open Classical in
/-- **The fingerprint error count.** Let `S` be a finite set of monic irreducible polynomials of
degree `k` over a field and `g i` (`i ∈ I`) a finite family of polynomials. The members of `S`
that divide some nonzero `g i` number at most `(∑ deg (g i)) / k`. With `g i = a - aᵢ`, the
difference between the pattern polynomial and the `i`-th text window, these are exactly the
moduli for which the fingerprint algorithm reports a false match, and the bound is Rabin's
`ℓ k = deg P ≤ deg H ≤ n m` (*Fingerprinting by random polynomials*, TR-15-81, 1981, proof of
Theorem 3, equations (5) and (6)). -/
theorem card_filter_exists_dvd_mul_le_sum_natDegree (S : Finset K[X]) (k : ℕ)
    (hS : ∀ f ∈ S, f.Monic ∧ Irreducible f ∧ f.natDegree = k) {ι : Type*} (I : Finset ι)
    (g : ι → K[X]) :
    (S.filter fun f => ∃ i ∈ I, g i ≠ 0 ∧ f ∣ g i).card * k ≤ ∑ i ∈ I, (g i).natDegree := by
  set J := I.filter fun i => g i ≠ 0
  set H := ∏ i ∈ J, g i
  have hH : H ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => (Finset.mem_filter.1 hi).2
  have hsub : (S.filter fun f => ∃ i ∈ I, g i ≠ 0 ∧ f ∣ g i) ⊆ S.filter (· ∣ H) := by
    intro f hf
    obtain ⟨hfS, i, hi, hgi, hdvd⟩ := Finset.mem_filter.1 hf
    refine Finset.mem_filter.2 ⟨hfS, hdvd.trans ?_⟩
    exact Finset.dvd_prod_of_mem g (Finset.mem_filter.2 ⟨hi, hgi⟩)
  have hdegH : H.natDegree ≤ ∑ i ∈ I, (g i).natDegree := by
    rw [natDegree_prod _ _ fun i hi => (Finset.mem_filter.1 hi).2]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  calc (S.filter fun f => ∃ i ∈ I, g i ≠ 0 ∧ f ∣ g i).card * k
      ≤ (S.filter (· ∣ H)).card * k := Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ H.natDegree := card_filter_dvd_mul_le_natDegree S k hS hH
    _ ≤ ∑ i ∈ I, (g i).natDegree := hdegH

/-- **Monic irreducible polynomials of prime degree over `ℤ/pℤ`.** For primes `p` and `k`, the
number `N` of monic irreducible polynomials of degree `k` over `ℤ/pℤ` satisfies `N k = p^k - p`:
the `p^k - p` elements of `GF(p^k)` outside `ℤ/pℤ` fall into the root sets of these polynomials,
`k` in each. This is the proof of Rabin's Lemma 1 (*Fingerprinting by random polynomials*,
TR-15-81, 1981, Section 2), given there for `p = 2`. -/
theorem ncard_monic_irreducible_mul_of_prime (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : k.Prime) :
    Set.ncard {f : (ZMod p)[X] | f.Monic ∧ Irreducible f ∧ f.natDegree = k} * k = p ^ k - p := by
  classical
  let K := GaloisField p k
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ k := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p k hk.ne_zero
  have hfin : Module.finrank (ZMod p) K = k := GaloisField.finrank p hk.ne_zero
  have hint : ∀ α : K, IsIntegral (ZMod p) α := fun α => Algebra.IsIntegral.isIntegral α
  -- the degree of a minimal polynomial is `1` or `k`
  have hdeg : ∀ α : K, (minpoly (ZMod p) α).natDegree = 1 ∨ (minpoly (ZMod p) α).natDegree = k := by
    intro α
    rw [← IntermediateField.adjoin.finrank (hint α)]
    apply hk.eq_one_or_self_of_dvd
    have h := Module.finrank_mul_finrank (ZMod p) (IntermediateField.adjoin (ZMod p) {α}) K
    rw [hfin] at h
    exact ⟨_, h.symm⟩
  -- every monic irreducible polynomial of degree `k` has a root in `K`
  have hroot : ∀ f : (ZMod p)[X], f.Monic → Irreducible f → f.natDegree = k →
      ∃ β : K, aeval β f = 0 := by
    intro f hmon hirr hdk
    have : Fact (Irreducible f) := ⟨hirr⟩
    let pb := AdjoinRoot.powerBasis hirr.ne_zero
    have : Module.Finite (ZMod p) (AdjoinRoot f) := pb.finite
    have : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod p)
    let _ : Fintype (AdjoinRoot f) := Fintype.ofFinite _
    have hcA : Fintype.card (AdjoinRoot f) = p ^ k := by
      rw [Module.card_fintype pb.basis, ZMod.card, Fintype.card_fin]
      simp [pb, AdjoinRoot.powerBasis_dim, hdk]
    let e := FiniteField.algEquivOfCardEq p (hcA.trans hcard.symm)
    refine ⟨e (AdjoinRoot.root f), ?_⟩
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply]
    simp
  -- the elements outside `ZMod p`
  let A : Finset K := Finset.univ.filter fun α => α ∉ (algebraMap (ZMod p) K).range
  have hrange : (Finset.univ.filter fun α : K => α ∈ (algebraMap (ZMod p) K).range).card = p := by
    have : (Finset.univ.filter fun α : K => α ∈ (algebraMap (ZMod p) K).range) =
        Finset.univ.image (algebraMap (ZMod p) K) := by
      ext α; simp [RingHom.mem_range]
    rw [this, Finset.card_image_of_injective _ (algebraMap (ZMod p) K).injective, Finset.card_univ,
      ZMod.card]
  have hA : A.card = p ^ k - p := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset K))
      (fun α => α ∈ (algebraMap (ZMod p) K).range)
    rw [Finset.card_univ, hcard, hrange] at h
    change (Finset.univ.filter fun α : K => α ∉ (algebraMap (ZMod p) K).range).card = p ^ k - p
    omega
  have hk1 : k ≠ 1 := hk.one_lt.ne'
  -- the set of polynomials is the image of `A` under `minpoly`
  have hT : {f : (ZMod p)[X] | f.Monic ∧ Irreducible f ∧ f.natDegree = k} =
      ((A.image fun α => minpoly (ZMod p) α : Finset _) : Set _) := by
    ext f
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, A,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hmon, hirr, hdk⟩
      obtain ⟨β, hβ⟩ := hroot f hmon hirr hdk
      have hmin := minpoly.eq_of_irreducible_of_monic hirr hβ hmon
      refine ⟨β, ?_, hmin.symm⟩
      rw [← minpoly.natDegree_eq_one_iff, ← hmin, hdk]
      exact hk1
    · rintro ⟨α, hα, rfl⟩
      refine ⟨minpoly.monic (hint α), minpoly.irreducible (hint α), ?_⟩
      rcases hdeg α with h | h
      · exact absurd (minpoly.natDegree_eq_one_iff.1 h) hα
      · exact h
  rw [hT, Set.ncard_coe_finset]
  -- each fibre is the root set, of size `k`
  have hfib : ∀ f ∈ A.image (fun α => minpoly (ZMod p) α),
      (A.filter fun α => minpoly (ZMod p) α = f).card = k := by
    intro f hf
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hf
    have hdk : (minpoly (ZMod p) α).natDegree = k := by
      rcases hdeg α with h | h
      · exact absurd (minpoly.natDegree_eq_one_iff.1 h) (Finset.mem_filter.1 hα).2
      · exact h
    have heq : (A.filter fun β => minpoly (ZMod p) β = minpoly (ZMod p) α) =
        ((minpoly (ZMod p) α).rootSet K).toFinset := by
      ext β
      simp only [Finset.mem_filter, A, Finset.mem_univ, true_and, Set.mem_toFinset,
        Polynomial.mem_rootSet]
      constructor
      · rintro ⟨-, h⟩
        rw [← h]
        exact ⟨minpoly.ne_zero (hint β), minpoly.aeval _ _⟩
      · rintro ⟨-, h⟩
        have hmin := minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (hint α)) h
          (minpoly.monic (hint α))
        refine ⟨?_, hmin.symm⟩
        rw [← minpoly.natDegree_eq_one_iff, ← hmin, hdk]
        exact hk1
    rw [heq, Set.toFinset_card]
    rw [card_rootSet_eq_natDegree (Algebra.IsSeparable.isSeparable (ZMod p) α)
      (Normal.splits inferInstance α), hdk]
  rw [← hA, Finset.card_eq_sum_card_image (fun α => minpoly (ZMod p) α) A,
    Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

/-- **Monic irreducible polynomials of prime degree over `ℤ₂`.** For a prime `k`, the number of
monic irreducible polynomials `x^k + a_{k-1} x^(k-1) + ⋯ + a₀ ∈ ℤ₂[x]` is `(2^k - 2)/k` (Rabin,
*Fingerprinting by random polynomials*, TR-15-81, 1981, Section 2, Lemma 1). For example `k = 2`
gives `1` (`x² + x + 1`) and `k = 3` gives `2`. -/
theorem ncard_monic_irreducible_zmod_two_of_prime {k : ℕ} (hk : k.Prime) :
    Set.ncard {f : (ZMod 2)[X] | f.Monic ∧ Irreducible f ∧ f.natDegree = k} = (2 ^ k - 2) / k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← ncard_monic_irreducible_mul_of_prime 2 hk, Nat.mul_div_cancel _ hk.pos]

end MetaMathlibExt.Fingerprint
