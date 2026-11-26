/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.KoszulFamilyPrimeFiltration
public import MathlibExt.Algebra.Homology.KoszulFamilyEulerLocalDimensionVanishing
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime

/-!
# Koszul Euler sums over the entire minimal support

Let N and M be finite modules over a noetherian local ring, with Ann N ⊆ Ann M, so Supp M ⊆
Supp N. For a family of n maximal-ideal elements, assume the post-quotients for both modules
have finite length and dim Supp N ≤ n. With a finite enumeration of the minimal support primes
of N, the Euler invariant for M is their full weighted sum.

The weight at p is ℓ_{R_p}(M_p), and the value is the coefficient-family Euler invariant on
R/p. These localized lengths are finite; zero weights retain primes outside the support of M.
The ring and both module carrier universes are independent.
-/

public section
noncomputable section
namespace Module
open CategoryTheory CategoryTheory.Limits

universe u v w

/-- Annihilator inclusion reverses supports.

For finite N, Ann N ⊆ Ann M implies Supp M ⊆ Supp N. -/
theorem support_subset_of_annihilator_le
    (S : Type u) [CommRing S]
    (N : Type v) [AddCommGroup N] [Module S N] [Module.Finite S N]
    (M : Type w) [AddCommGroup M] [Module S M]
    (hAnn : Module.annihilator S N ≤ Module.annihilator S M) :
    Module.support S M ⊆ Module.support S N := by
  intro p hp
  exact Module.mem_support_iff_of_finite.mpr
    (hAnn.trans (Module.annihilator_le_of_mem_support hp))

/-- The minimal primes of a module's support.

Take the subtype of prime-spectrum points minimal among those in Supp(N). -/
abbrev minimalSupportPrimes
    (S : Type u) [CommRing S]
    (N : Type v) [AddCommGroup N] [Module S N] :=
  {p : PrimeSpectrum S // Minimal (fun q => q ∈ Module.support S N) p}

/-- The Koszul Euler contribution at a reference minimal-support prime.

For p minimal in Supp(N), use the post-quotient finiteness to define the family coefficient
Euler value on R/p. -/
def koszulFamilyMinimalSupportPrimeValue
    (S : Type u) [CommRing S] [IsNoetherianRing S]
    (N : Type v) [AddCommGroup N] [Module S N]
    {n : ℕ} (c : Fin n → S)
    (hPost : Module.length S
      (S ⧸ (Ideal.span (Set.range c) ⊔ Module.annihilator S N)) ≠ ⊤)
    (p : minimalSupportPrimes S N) : ℤ :=
  let J := Ideal.span (Set.range c) ⊔ p.1.asIdeal
  let hJ : Module.length S (S ⧸ J) ≠ ⊤ :=
    Module.length_ne_top_of_finite_of_ideal_le_annihilator S (S ⧸ J)
      (Ideal.span (Set.range c) ⊔ Module.annihilator S N)
      (by
        rw [Ideal.annihilator_quotient]
        exact sup_le_sup_left (Module.annihilator_le_of_mem_support p.2.1) _) hPost
  (Module.KoszulFamilyEulerPrimeFactor.mk p.1 hJ).value S

private theorem branchEuler_list_sum_exchange
    {A : Type v} {B : Type w} [Fintype B] (l : List A) (f : A → B → ℤ) :
    (l.map fun a => ∑ b, f a b).sum = ∑ b, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [ih]

private theorem branchEuler_list_sum_count
    {A : Type v} (l : List A) (p : A → Prop) [DecidablePred p] (z : ℤ) :
    (l.map fun a => if p a then z else 0).sum =
      (l.countP (fun a => decide (p a)) : ℤ) * z := by
  rw [List.sum_map_ite]
  simp [List.countP_eq_length_filter]

private theorem koszulFamilyFactor_minimal_support_of_value_ne_zero
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (N : Type v) [AddCommGroup N] [Module S N] [Module.Finite S N]
    (M : Type w) [AddCommGroup M] [Module S M]
    {n : ℕ} (c : Fin n → S)
    (hAnn : Module.annihilator S N ≤ Module.annihilator S M)
    (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal S)
    (hDim : Module.supportDim S N ≤ n)
    (d : Module.KoszulFamilyEulerPrimeDecomposition S c M)
    (f : Module.KoszulFamilyEulerPrimeFactor S c) (hf : f ∈ d.factors)
    (hvalue : f.value S ≠ 0) :
    Minimal (fun p => p ∈ Module.support S N) f.prime := by
  have hfN : f.prime ∈ Module.support S N :=
    support_subset_of_annihilator_le S N M hAnn (d.factor_mem_support f hf)
  refine ⟨hfN, ?_⟩
  intro p hp hle
  by_cases heq : p = f.prime
  · exact heq ▸ le_rfl
  have hlt : p < f.prime := lt_of_le_of_ne hle heq
  have hdrop : Module.supportDim S (S ⧸ f.prime.asIdeal) < n :=
    Module.supportDim_quotient_lt_of_lt_of_mem_support S N f.prime p hfN hp hlt hDim
  have hquot : Module.length S
      (S ⧸ (Ideal.span (Set.range c) ⊔ Module.annihilator S (S ⧸ f.prime.asIdeal))) ≠ ⊤ := by
    rw [Ideal.annihilator_quotient]
    exact f.quotient_length_ne_top
  have hzero : f.value S = 0 :=
    KoszulComplex.familyTensorCoefficientEuler_eq_zero_of_supportDim_lt
      S c (S ⧸ f.prime.asIdeal) hquot hc hdrop
  exact False.elim (hvalue hzero)

/-- The full reference-minimal-support Euler formula.

Under the stated local, annihilator, quotient and dimension hypotheses, all M_p lengths on the
minimal support of N are finite and their weighted prime values sum to the Euler invariant of
M. -/
theorem koszulFamilyEuler_eq_sum_minimalSupport
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (N : Type v) [AddCommGroup N] [Module S N] [Module.Finite S N]
    (M : Type w) [AddCommGroup M] [Module S M] [Module.Finite S M]
    {n : ℕ} (c : Fin n → S)
    (hPostN : Module.length S
      (S ⧸ (Ideal.span (Set.range c) ⊔ Module.annihilator S N)) ≠ ⊤)
    (hPostM : Module.length S
      (S ⧸ (Ideal.span (Set.range c) ⊔ Module.annihilator S M)) ≠ ⊤)
    (hAnn : Module.annihilator S N ≤ Module.annihilator S M)
    (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal S)
    (hDim : Module.supportDim S N ≤ n)
    [Fintype (minimalSupportPrimes S N)] :
    (∀ p : minimalSupportPrimes S N,
      Module.length (Localization.AtPrime p.1.asIdeal)
        (LocalizedModule.AtPrime p.1.asIdeal M) ≠ ⊤) ∧
    KoszulComplex.familyTensorCoefficientEuler S c (ModuleCat.of S M) hPostM =
      ∑ p : minimalSupportPrimes S N,
        ((Module.length (Localization.AtPrime p.1.asIdeal)
          (LocalizedModule.AtPrime p.1.asIdeal M)).toNat : ℤ) *
            koszulFamilyMinimalSupportPrimeValue S N c hPostN p := by
  classical
  obtain ⟨d⟩ := Module.exists_koszulFamilyEulerPrimeDecomposition S c M hPostM
  have hsupport := support_subset_of_annihilator_le S N M hAnn
  have hcount (p : minimalSupportPrimes S N) :
      Module.length (Localization.AtPrime p.1.asIdeal)
        (LocalizedModule.AtPrime p.1.asIdeal M) =
      (d.factors.countP (fun f => decide (f.prime = p.1)) : ℕ) :=
    d.localized_length_eq_countP_of_minimal S p.1
      (fun q hq hle => le_antisymm hle (p.2.2 (hsupport hq) hle))
  constructor
  · intro p
    rw [hcount p]
    simp
  have hfactor (f : Module.KoszulFamilyEulerPrimeFactor S c) (hf : f ∈ d.factors) :
      f.value S = ∑ p : minimalSupportPrimes S N,
        if f.prime = p.1 then koszulFamilyMinimalSupportPrimeValue S N c hPostN p else 0 := by
    by_cases hmin : Minimal (fun p => p ∈ Module.support S N) f.prime
    · let p : minimalSupportPrimes S N := ⟨f.prime, hmin⟩
      symm
      rw [Finset.sum_eq_single p]
      · simp only [p, ↓reduceIte]
        rfl
      · intro q _ hqp
        have hne : f.prime ≠ q.1 := by
          intro heq
          exact hqp (Subtype.ext heq.symm)
        simp only [hne, ↓reduceIte]
      · intro hp
        exact False.elim (hp (Finset.mem_univ p))
    · have hzero : f.value S = 0 := by
        by_contra hvalue
        exact hmin (koszulFamilyFactor_minimal_support_of_value_ne_zero
          S N M c hAnn hc hDim d f hf hvalue)
      rw [hzero]
      symm
      apply Finset.sum_eq_zero
      intro p _
      have hne : f.prime ≠ p.1 := by
        intro heq
        apply hmin
        simpa only [heq] using p.2
      simp only [hne, ↓reduceIte]
  calc
    KoszulComplex.familyTensorCoefficientEuler S c (ModuleCat.of S M) hPostM =
        (d.factors.map (Module.KoszulFamilyEulerPrimeFactor.value S)).sum :=
      d.eq_sum_familyTensorCoefficientEuler S hPostM
    _ = (d.factors.map fun f => ∑ p : minimalSupportPrimes S N,
        if f.prime = p.1 then koszulFamilyMinimalSupportPrimeValue S N c hPostN p else 0).sum := by
      rw [List.map_congr_left hfactor]
    _ = ∑ p : minimalSupportPrimes S N,
        (d.factors.map fun f =>
          if f.prime = p.1 then koszulFamilyMinimalSupportPrimeValue S N c hPostN p else 0).sum :=
      branchEuler_list_sum_exchange d.factors _
    _ = ∑ p : minimalSupportPrimes S N,
        (d.factors.countP (fun f => decide (f.prime = p.1)) : ℤ) *
          koszulFamilyMinimalSupportPrimeValue S N c hPostN p := by
      apply Finset.sum_congr rfl
      intro p _
      exact branchEuler_list_sum_count d.factors
        (fun f => f.prime = p.1) (koszulFamilyMinimalSupportPrimeValue S N c hPostN p)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hcount p, ENat.toNat_natCast]

/-- A row with the same homology lengths has the same Koszul Euler sum.

If E_j has the length of H_j(K(a;M)) for every j, its alternating sum through n equals the
coefficient-family Euler invariant. -/
theorem koszulFamilyEuler_row_eq_of_homology_lengths
    (S : Type u) [CommRing S] [IsNoetherianRing S]
    {n : ℕ} (c : Fin n → S) (M : ModuleCat.{v} S) [Module.Finite S M]
    (E : ℕ → ModuleCat.{w} S)
    (hPost : Module.length S
      (S ⧸ (Ideal.span (Set.range c) ⊔ Module.annihilator S M)) ≠ ⊤)
    (hE : ∀ p, Module.length S ((KoszulComplex.familyTensorCoefficientComplex S c M).homology p) =
      Module.length S (E p)) :
    (∑ p ∈ Finset.range (n + 1), (-1 : ℤ) ^ p * (Module.length S (E p)).toNat) =
      KoszulComplex.familyTensorCoefficientEuler S c M hPost := by
  symm
  apply (KoszulComplex.familyTensorCoefficientEuler_eq S c M hPost).trans
  apply Finset.sum_congr rfl
  intro p _
  exact congrArg (fun l : ENat => (-1 : ℤ) ^ p * (l.toNat : ℤ)) (hE p)

/-- The minimal-support Euler formula for bundled coefficient modules.

For bundled finite N and M under the same hypotheses, the Euler invariant of M equals the full
sum over minimal support primes of N. -/
theorem koszulFamilyEuler_moduleCat_eq_sum_minimalSupport
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (N : ModuleCat.{v} S) [Module.Finite S N] (M : ModuleCat.{w} S) [Module.Finite S M]
    {n : ℕ} (c : Fin n → S)
    (hPostN : Module.length S
      (S ⧸ (Ideal.span (Set.range c) ⊔ Module.annihilator S N)) ≠ ⊤)
    (hPostM : Module.length S
      (S ⧸ (Ideal.span (Set.range c) ⊔ Module.annihilator S M)) ≠ ⊤)
    (hAnn : Module.annihilator S N ≤ Module.annihilator S M)
    (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal S) (hDim : Module.supportDim S N ≤ n)
    [Fintype (minimalSupportPrimes S N)] :
    KoszulComplex.familyTensorCoefficientEuler S c M hPostM =
      ∑ p : minimalSupportPrimes S N,
        ((Module.length (Localization.AtPrime p.1.asIdeal)
          (LocalizedModule.AtPrime p.1.asIdeal M)).toNat : ℤ) *
            koszulFamilyMinimalSupportPrimeValue S N c hPostN p :=
  (koszulFamilyEuler_eq_sum_minimalSupport S N M c hPostN hPostM hAnn hc hDim).2

end Module
