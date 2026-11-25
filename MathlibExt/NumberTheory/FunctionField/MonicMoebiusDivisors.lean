/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Möbius sums over monic divisors

The sum of the Möbius function divided by the polynomial norm over the monic divisors
of a monic polynomial is an Euler product over its distinct monic irreducible factors.
-/

open Polynomial UniqueFactorizationMonoid

namespace MetaMathlibExt
namespace monic_sum_moebius_div_norm

variable {F : Type*} [Field F] [DecidableEq F] {f : F[X]}

private theorem factors_prod {s : Finset F[X]} (hs : s.val ⊆ normalizedFactors f) :
    normalizedFactors (s.prod id) = s.val := by
  rw [← Finset.prod_val, normalizedFactors_prod_eq _ fun p hp ↦
    irreducible_of_normalized_factor p (hs hp)]
  exact (Multiset.map_congr rfl fun p hp ↦ normalize_normalized_factor p (hs hp)).trans
    (Multiset.map_id _)

-- Products of subsets of the distinct prime factors index the squarefree monic divisors.
private theorem sum_over_subsets (hf : f.Monic) (w : F[X] → ℝ)
    (hw : ∀ g, ¬ Squarefree g → w g = 0) :
    ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f}, w g =
      ∑ s ∈ (normalizedFactors f).toFinset.powerset, w (s.prod id) := by
  classical
  let primes := (normalizedFactors f).toFinset
  have sub {s : Finset F[X]} (hs : s ∈ primes.powerset) : s.val ⊆ normalizedFactors f :=
    fun _ hp ↦ Multiset.mem_toFinset.mp (Finset.mem_powerset.mp hs hp)
  let product (s : Finset F[X]) := s.prod id
  calc
    _ = ∑ g ∈ primes.powerset.image product, w g := by
      apply finsum_cond_eq_sum_of_cond_iff
      intro g hne
      constructor
      · rintro ⟨hm, hd⟩
        have hsq : Squarefree g := by_contra fun h ↦ hne (hw g h)
        let s : Finset F[X] := ⟨normalizedFactors g,
          (squarefree_iff_nodup_normalizedFactors hm.ne_zero).mp hsq⟩
        refine Finset.mem_image.mpr ⟨s, Finset.mem_powerset.mpr ?_, ?_⟩
        · intro p hp
          exact Multiset.mem_toFinset.mpr
            (Multiset.subset_of_le ((dvd_iff_normalizedFactors_le_normalizedFactors
              hm.ne_zero hf.ne_zero).mp hd) hp)
        · exact (Finset.prod_val s).symm.trans
            ((prod_normalizedFactors_eq hm.ne_zero).trans hm.normalize_eq_self)
      · intro hg
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hg
        have hm : (product s).Monic := monic_prod_of_monic _ _ fun p hp ↦
          ((Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp (sub hs hp)).2.1
        refine ⟨hm, (dvd_iff_normalizedFactors_le_normalizedFactors hm.ne_zero hf.ne_zero).mpr ?_⟩
        rw [show normalizedFactors (product s) = s.val from factors_prod (sub hs)]
        exact (Multiset.le_iff_subset s.nodup).mpr (sub hs)
    _ = _ := by
      apply Finset.sum_image
      intro s hs t ht he
      exact Finset.val_injective <| (factors_prod (sub hs)).symm.trans
        ((congrArg normalizedFactors he).trans (factors_prod (sub ht)))

end monic_sum_moebius_div_norm

open monic_sum_moebius_div_norm in
/-- **Möbius sum over the monic divisors of a polynomial over a finite field.** Let $F$ be a finite
field with $q$ elements and let $\mu$ be the Möbius function of $F[T]$. For every monic
$f \in F[T]$,

$$\sum_{g \text{ monic},\ g \mid f} \frac{\mu(g)}{q^{\deg g}} =
\prod_{P \text{ monic irreducible},\ P \mid f} \left(1 - \frac{1}{q^{\deg P}}\right).$$

The right side is $\Phi(f) / q^{\deg f}$, where $\Phi$ is Euler's totient function on $F[T]$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 6
(`integers-2026-A80-lem-6`); `Φ` as defined after Theorem 3. -/
public theorem monic_sum_moebius_div_norm {F : Type*} [Field F] [Fintype F] {f : F[X]}
    (hf : f.Monic) :
    ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f},
        (moebius g : ℝ) / (Fintype.card F : ℝ) ^ g.natDegree =
      ∏ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ f},
        (1 - 1 / (Fintype.card F : ℝ) ^ P.natDegree) := by
  classical
  let primes := (normalizedFactors f).toFinset
  have hmem (p : F[X]) : p ∈ primes ↔ p.Monic ∧ Irreducible p ∧ p ∣ f := by
    simp only [primes, Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hf.ne_zero]
    tauto
  have hset : {p : F[X] | p.Monic ∧ Irreducible p ∧ p ∣ f} = ↑primes :=
    Set.ext fun p ↦ (hmem p).symm
  rw [hset, finprod_mem_coe_finset, sum_over_subsets hf _ (fun g hg ↦ by
    simp [moebius_of_not_squarefree hg])]
  simp_rw [sub_eq_add_neg, ← neg_div, Finset.prod_one_add]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hsub : s ⊆ primes := Finset.mem_powerset.mp hs
  have hm (p) (hp : p ∈ s) := ((hmem p).mp (hsub hp)).1
  have hfac : normalizedFactors (s.prod id) = s.val :=
    factors_prod (fun _ hp ↦ Multiset.mem_toFinset.mp (hsub hp))
  have hsq : Squarefree (s.prod id) :=
    (squarefree_iff_nodup_normalizedFactors (monic_prod_of_monic s id hm).ne_zero).mpr
      (hfac.symm ▸ s.nodup)
  have hcard : (factors (s.prod id)).card = s.card := by
    simpa only [normalizedFactors, Multiset.card_map, Finset.card_val] using
      congrArg Multiset.card hfac
  rw [hsq.moebius_eq, hcard, Int.cast_pow, Int.cast_neg, Int.cast_one,
    natDegree_prod_of_monic s id hm, Finset.prod_div_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum]
  rfl

end MetaMathlibExt
