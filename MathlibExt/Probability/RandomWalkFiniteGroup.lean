/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.FiniteAbelianDFT
public import MathlibExt.Analysis.Fourier.FiniteGroupYoung
public import MathlibExt.Probability.MarkovMixing
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.GroupTheory.Perm.Support
public import MathlibExt.RepresentationTheory.FourierTransformFiniteGroup
public import MathlibExt.RepresentationTheory.FourierPlancherel

import MathlibExt.GroupTheory.BurnsidePaqb.CharacterOrthogonality

import Mathlib.GroupTheory.Perm.Centralizer

import MathlibExt.Analysis.Fourier.FiniteAbelianUncertainty
import Mathlib.Algebra.Order.Chebyshev

/-!
# Random walks on finite groups: the upper bound lemma

A random walk on a finite group `G` driven by a probability `Q` has `k`-step law the convolution
power `Q^{*k}`; its distance to the uniform distribution `U` is measured in total variation
`‖Q^{*k} - U‖ = (1/2) ∑_s |Q^{*k}(s) - U(s)|` (`MathlibExt.Probability.MarkovMixing.tvDist`).
Diaconis and Shahshahani bound this distance by the Fourier transform of `Q` at the non-trivial
irreducible representations (the *upper bound lemma*). This file proves the lemma on every finite
group (`upper_bound_lemma`, from the Plancherel formula
`MathlibExt.RepresentationTheory.FourierPlancherel.plancherel`), and in the explicit form used for
finite abelian groups, where the irreducible representations are the characters `ψ : G → ℂ` and
the transform is `MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted.dftFun`:

* `four_mul_tvDist_uniform_sq_le`: `4 ‖P - U‖² ≤ ∑_{ψ ≠ 1} |P̂(ψ)|²`;
* `dftFun_finGroupConv`: the transform of a convolution is the product of the transforms;
* `four_mul_tvDist_addConvPow_sq_le`: `4 ‖P^{*k} - U‖² ≤ ∑_{ψ ≠ 1} |P̂(ψ)|^{2k}`;
* `upper_bound_lemma`: on any finite group, `4 ‖P - U‖² ≤ ∑_ρ d_ρ Tr(P̂(ρ) P̂(ρ)*)` over the
  non-trivial irreducible representations;
* `fourier_randomTransposition`: the Fourier transform of the random-transposition measure at an
  irreducible representation `ρ` of `Sₙ` is the scalar `1/n + ((n-1)/n) χ_ρ(τ)/d_ρ`;
* `four_mul_tvDist_randomTransposition_sq_le`: hence
  `4 ‖T^{*k} - U‖² ≤ ∑_ρ d_ρ² (1/n + ((n-1)/n) χ_ρ(τ)/d_ρ)^{2k}` over the non-trivial irreducible
  representations of `Sₙ`, the inequality from which Diaconis and Shahshahani start their
  character estimates.

It also records the uniform distribution and the random-transposition measure on the symmetric
group, the walk of Diaconis and Shahshahani (1981).

Sources: P. Diaconis, *Applications of non-commutative Fourier analysis to probability problems*,
École d'Été de Probabilités de Saint-Flour XV–XVII, Lecture Notes in Math. 1362 (1988) 51–100,
Lemma 2.1, equation (3.3) and Lemma 4.2; P. Diaconis and M. Shahshahani, *Generating a random
permutation with random transpositions*, Z. Wahrsch. Verw. Gebiete 57 (1981) 159–179, (1.1).
-/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Probability.RandomWalkFiniteGroup

open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted (dftFun)
open MathlibExt.Analysis.Fourier (finGroupConv)
open MathlibExt.Probability.MarkovMixing (tvDist)

/-- **The uniform distribution on a finite nonempty set.** `U(s) = 1/|G|` for every `s`; it is
the stationary law of every random walk on a finite group (Diaconis and Shahshahani 1981, (1.2)).
For an empty set, which is excluded, the total mass would be `0`. -/
noncomputable def uniform (G : Type*) [Fintype G] [Nonempty G] : G → ℝ :=
  fun _ => ((Fintype.card G : ℝ))⁻¹

open Classical in
/-- **The random-transposition measure on the symmetric group.** Two positions `L`, `R` are chosen
independently and uniformly among `n ≥ 1` and the cards there are swapped (nothing happens when
`L = R`). Its law is `T(id) = 1/n`, `T(τ) = 2/n²` for each transposition `τ`, and `T = 0`
elsewhere (Diaconis and Shahshahani 1981, (1.1)). For `n = 0`, which is excluded, the identity
would get mass `1/0 = 0` and the law total mass `0`. -/
noncomputable def randomTransposition (n : ℕ) [NeZero n] : Equiv.Perm (Fin n) → ℝ :=
  fun σ => if σ = 1 then 1 / n else if σ.IsSwap then 2 / (n : ℝ) ^ 2 else 0

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- **Convolution powers on a finite abelian group.** `addConvPow f 0` is the point mass at `0`
and `addConvPow f (k + 1) = f * addConvPow f k` for the convolution
`MathlibExt.Analysis.Fourier.finGroupConv`; for a probability `f` it is the law after `k` steps
of the random walk driven by `f` (Diaconis, Saint-Flour notes 1988, Section 2). -/
noncomputable def addConvPow [DecidableEq G] (f : G → ℂ) : ℕ → G → ℂ
  | 0 => fun x => if x = 0 then 1 else 0
  | k + 1 => finGroupConv f (addConvPow f k)

/-- **Convolution theorem on a finite abelian group.** The Fourier transform of `f * g` at a
character `ψ` is `f̂(ψ) ĝ(ψ)` (Diaconis, Saint-Flour notes 1988, Section 2: "transforms turn
convolution into multiplication"). -/
theorem dftFun_finGroupConv (f g : G → ℂ) (ψ : AddChar G ℂ) :
    dftFun (finGroupConv f g) ψ = dftFun f ψ * dftFun g ψ := by
  simp only [dftFun, finGroupConv, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Equiv.sum_comp (Equiv.addLeft y)]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Equiv.coe_addLeft, add_sub_cancel_left, AddChar.map_add_eq_mul]
  ring

/-- **Fourier transform of a convolution power on a finite abelian group.** For every character
`ψ`, the transform of the `k`-th convolution power of `f` is `f̂(ψ)^k` (iterate
`dftFun_finGroupConv`; Diaconis, Saint-Flour notes 1988, Section 2). -/
theorem dftFun_addConvPow [DecidableEq G] (f : G → ℂ) (k : ℕ) (ψ : AddChar G ℂ) :
    dftFun (addConvPow f k) ψ = dftFun f ψ ^ k := by
  induction k with
  | zero => simp [dftFun, addConvPow]
  | succ k ih => rw [addConvPow, dftFun_finGroupConv, ih, pow_succ']

/-- **Upper bound lemma on a finite abelian group.** For `P : G → ℝ` with total mass `1` and `U`
the uniform distribution, `4 ‖P - U‖²_TV ≤ ∑_{ψ ≠ 1} |P̂(ψ)|²`, the sum running over the
non-trivial characters (Diaconis, Saint-Flour notes 1988, Lemma 2.1 for `ℤ/n` and the abelian case
of Lemma 4.2; the proof is theirs: Cauchy–Schwarz, then Plancherel, using `P̂(1) = Û(1) = 1` and
`Û(ψ) = 0` for `ψ ≠ 1`). -/
theorem four_mul_tvDist_uniform_sq_le (P : G → ℝ) (hP : ∑ x, P x = 1) :
    4 * tvDist P (uniform G) ^ 2 ≤
      ∑ ψ ∈ Finset.univ.filter (fun ψ : AddChar G ℂ => ψ ≠ 0),
        ‖dftFun (fun x => (P x : ℂ)) ψ‖ ^ 2 := by
  classical
  set N : ℝ := (Fintype.card G : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set f : G → ℝ := fun x => P x - N⁻¹ with hf
  -- Step 1: `4 tv² = (∑ |f|)² ≤ N ∑ f²` (Cauchy–Schwarz).
  have h1 : 4 * tvDist P (uniform G) ^ 2 = (∑ x, |f x|) ^ 2 := by
    simp only [tvDist, uniform, hf, hN]; ring
  have h2 : (∑ x, |f x|) ^ 2 ≤ N * ∑ x, f x ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun x => |f x|)
    simpa [sq_abs, hN] using this
  -- Step 2: Plancherel, `N ∑ f² = ∑_ψ |f̂ ψ|²`.
  have h3 : N * ∑ x, f x ^ 2 = ∑ ψ : AddChar G ℂ, ‖dftFun (fun x => (f x : ℂ)) ψ‖ ^ 2 := by
    rw [MathlibExt.Analysis.Fourier.FiniteAbelianUncertainty.sum_norm_sq_dftFun]
    simp [hN, Complex.norm_real, sq_abs]
  -- Step 3: `f̂(0) = 0` and `f̂(ψ) = P̂(ψ)` for `ψ ≠ 0`.
  have hsumf : ∑ x, f x = 0 := by
    simp only [hf, Finset.sum_sub_distrib, hP, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← hN, mul_inv_cancel₀ hNpos.ne', sub_self]
  have h0 : dftFun (fun x => (f x : ℂ)) 0 = 0 := by
    simp only [dftFun, AddChar.zero_apply, one_mul]
    exact_mod_cast hsumf
  have hne : ∀ ψ : AddChar G ℂ, ψ ≠ 0 →
      dftFun (fun x => (f x : ℂ)) ψ = dftFun (fun x => (P x : ℂ)) ψ := fun ψ hψ => by
    have hψs : ∑ x, ψ x = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hψ
    simp only [dftFun, hf, Complex.ofReal_sub, Complex.ofReal_inv, mul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hψs, zero_mul, sub_zero]
  have h4 : ∑ ψ : AddChar G ℂ, ‖dftFun (fun x => (f x : ℂ)) ψ‖ ^ 2 =
      ∑ ψ ∈ Finset.univ.filter (fun ψ : AddChar G ℂ => ψ ≠ 0),
        ‖dftFun (fun x => (P x : ℂ)) ψ‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ψ : AddChar G ℂ => ψ ≠ 0)]
    have hz : ∑ ψ ∈ Finset.univ.filter (fun ψ : AddChar G ℂ => ¬ψ ≠ 0),
        ‖dftFun (fun x => (f x : ℂ)) ψ‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun ψ hψ => ?_
      simp only [Finset.mem_filter, not_not] at hψ
      rw [hψ.2, h0, norm_zero]; ring
    rw [hz, add_zero]
    refine Finset.sum_congr rfl fun ψ hψ => ?_
    rw [hne ψ (Finset.mem_filter.mp hψ).2]
  rw [h1, ← h4, ← h3]
  exact h2

/-- **Upper bound lemma for a random walk on a finite abelian group.** If `P : G → ℝ` has total
mass `1` and `Q` is its `k`-th convolution power (`Q = P^{*k}`, cast to `ℂ`), then
`4 ‖Q - U‖²_TV ≤ ∑_{ψ ≠ 1} |P̂(ψ)|^{2k}` (Diaconis, Saint-Flour notes 1988, equation (3.3) for the
cube `ℤ₂ⁿ`, and the bound used in the proof of Theorem 2.1 for `ℤ/n`). -/
theorem four_mul_tvDist_addConvPow_sq_le [DecidableEq G] (P Q : G → ℝ) (hP : ∑ x, P x = 1)
    (k : ℕ) (hQ : ∀ x, (Q x : ℂ) = addConvPow (fun x => (P x : ℂ)) k x) :
    4 * tvDist Q (uniform G) ^ 2 ≤
      ∑ ψ ∈ Finset.univ.filter (fun ψ : AddChar G ℂ => ψ ≠ 0),
        ‖dftFun (fun x => (P x : ℂ)) ψ‖ ^ (2 * k) := by
  have hQfun : (fun x => (Q x : ℂ)) = addConvPow (fun x => (P x : ℂ)) k := funext hQ
  have hdft : ∀ ψ, dftFun (fun x => (Q x : ℂ)) ψ = dftFun (fun x => (P x : ℂ)) ψ ^ k :=
    fun ψ => by rw [hQfun, dftFun_addConvPow]
  have hQ1 : ∑ x, Q x = 1 := by
    have h := hdft 0
    simp only [dftFun, AddChar.zero_apply, one_mul] at h
    rw [show (∑ x, (P x : ℂ)) = 1 by exact_mod_cast hP, one_pow] at h
    exact_mod_cast h
  refine (four_mul_tvDist_uniform_sq_le Q hQ1).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [hdft, norm_pow, ← pow_mul, mul_comm]

section RandomTransposition

open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup (fourier
  fourier_eq_smul_one_of_isClassFunction nontrivial_of_isIrreducible)

/-- **The random-transposition measure is a class function.** `T(h σ h⁻¹) = T(σ)` for all
`σ, h ∈ Sₙ`, since conjugation fixes the identity and maps transpositions to transpositions
(Diaconis and Shahshahani 1981, proof of Corollary 1). -/
theorem randomTransposition_conj (n : ℕ) [NeZero n] (σ h : Equiv.Perm (Fin n)) :
    randomTransposition n (h * σ * h⁻¹) = randomTransposition n σ := by
  classical
  have h1 : h * σ * h⁻¹ = 1 ↔ σ = 1 := by
    rw [mul_inv_eq_one]
    constructor
    · intro e; simpa using congrArg (h⁻¹ * ·) e
    · rintro rfl; simp
  have h2 : (h * σ * h⁻¹).IsSwap ↔ σ.IsSwap := by
    rw [← Equiv.Perm.card_support_eq_two, ← Equiv.Perm.card_support_eq_two,
      Equiv.Perm.card_support_conj]
  simp only [randomTransposition, h1, h2]

open Classical in
/-- **Number of transpositions in the symmetric group.** For `n ≥ 2`, `Sₙ` has `C(n, 2)`
transpositions, stated as `2 #{τ} = n (n - 1)` (Diaconis and Shahshahani 1981, proof of
Corollary 1: "there are `C(n, 2)` transpositions"). -/
theorem two_mul_card_isSwap (n : ℕ) (hn : 2 ≤ n) :
    2 * (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.IsSwap)).card = n * (n - 1) := by
  classical
  have hc : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.IsSwap)) =
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.cycleType = {2})) := by
    ext σ; simp [Equiv.Perm.isSwap_iff_cycleType]
  rw [hc, Equiv.Perm.card_of_cycleType]
  simp only [Multiset.sum_singleton, Fintype.card_fin, Multiset.mem_singleton, forall_eq,
    le_refl, and_true, hn, ite_true, Multiset.prod_singleton, Multiset.toFinset_singleton,
    Finset.prod_singleton, Multiset.count_singleton_self, Nat.factorial_one, mul_one]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + m - 2 = m by omega, show 2 + m - 1 = m + 1 by omega,
    show 2 + m = m + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
  rw [show (m + 1 + 1) * ((m + 1) * m.factorial) = ((m + 1 + 1) * (m + 1)) * m.factorial by ring,
    mul_comm m.factorial 2, Nat.mul_div_mul_right _ _ m.factorial_pos]
  have : 2 ∣ (m + 1 + 1) * (m + 1) := by
    rcases Nat.even_or_odd (m + 1) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Dvd.dvd.mul_left ⟨r, by omega⟩ _
    · exact Dvd.dvd.mul_right ⟨r + 1, by omega⟩ _
  rw [Nat.mul_div_cancel' this]

/-- **Fourier transform of the random-transposition measure.** Let `ρ` be an irreducible
representation of `Sₙ` on a finite-dimensional complex space of dimension `d_ρ`, and `τ` any
transposition. Then `T̂(ρ) = (1/n + ((n - 1)/n) χ_ρ(τ)/d_ρ) • 1` (Diaconis and Shahshahani 1981,
Corollary 1, proved there from Lemma 5 as here). -/
theorem fourier_randomTransposition {n : ℕ} [NeZero n] {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible]
    (τ : Equiv.Perm (Fin n)) (hτ : τ.IsSwap) :
    fourier ρ (fun σ => (randomTransposition n σ : ℂ)) =
      ((1 : ℂ) / n + ((n : ℂ) - 1) / n * (ρ.character τ / Module.finrank ℂ V)) • 1 := by
  classical
  have hn : 2 ≤ n := by
    have h2 := Equiv.Perm.card_support_eq_two.mpr hτ
    have := Finset.card_le_univ τ.support
    simp only [Fintype.card_fin] at this
    omega
  rw [fourier_eq_smul_one_of_isClassFunction ρ _ (fun g h => by
    simp only [randomTransposition_conj])]
  congr 1
  set S := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.IsSwap) with hS
  have hchar : ∀ σ ∈ S, ρ.character σ = ρ.character τ := fun σ hσ => by
    obtain ⟨x, y, hxy, rfl⟩ := (Finset.mem_filter.mp hσ).2
    obtain ⟨a, b, hab, rfl⟩ := hτ
    obtain ⟨c, hc⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hxy hab)
    rw [← hc, Representation.char_conj]
  have hpt : ∀ σ : Equiv.Perm (Fin n), (randomTransposition n σ : ℂ) * ρ.character σ =
      (if σ = 1 then ρ.character 1 / n else 0) +
        (if σ.IsSwap then 2 / (n : ℂ) ^ 2 * ρ.character τ else 0) := fun σ => by
    by_cases h1 : σ = 1
    · subst h1
      have : ¬ (1 : Equiv.Perm (Fin n)).IsSwap := fun h => by
        simpa using Equiv.Perm.card_support_eq_two.mpr h
      simp [randomTransposition, this]
      ring
    · by_cases h2 : σ.IsSwap
      · simp [randomTransposition, h1, h2, hchar σ (by simp [hS, h2])]
      · simp [randomTransposition, h1, h2]
  have hsum : ∑ σ, (randomTransposition n σ : ℂ) * ρ.character σ =
      ρ.character 1 / n + S.card * (2 / (n : ℂ) ^ 2 * ρ.character τ) := by
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hS]
  have hcard : (2 : ℂ) * S.card = n * (n - 1) := by
    have := two_mul_card_isSwap n hn
    rw [hS]
    exact_mod_cast (by rw [this]; push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring :
      ((2 * S.card : ℕ) : ℂ) = (n : ℂ) * (n - 1))
  have := nontrivial_of_isIrreducible ρ
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hsum, Representation.char_one]
  have hS' : (S.card : ℂ) = n * (n - 1) / 2 := by
    rw [eq_div_iff two_ne_zero, mul_comm]; exact hcard
  rw [hS']
  field_simp

end RandomTransposition

section UpperBoundLemma

open CategoryTheory
open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup (fourier fourier_uniform_eq_zero
  convPow)

open Classical in
/-- **Upper bound lemma (Diaconis–Shahshahani).** Let `V : ι → FDRep ℂ G` be a complete set of
irreducible complex representations of the finite group `G` (pairwise non-isomorphic simple
objects, every simple object isomorphic to one of them), of dimensions `d_i`, and let
`P : G → ℝ` have total mass `1`. Then `4 ‖P - U‖²_TV ≤ ∑_i d_i Tr(P̂(V_i) P̂(V_i)*)`, the sum
running over the non-trivial irreducible representations (those with some `ρ(g) ≠ 1`)
(Diaconis, Saint-Flour notes 1988, Lemma 4.2, "first used by Diaconis and Shahshahani (1981)";
the lemma is printed with `=` but its proof, Cauchy–Schwarz then Plancherel, gives `≤`, which is
what is stated here). The source takes `ρ` unitary; then, for real `P`,
`P̂(ρ)* = ∑_s P(s) ρ(s⁻¹)` is the transform of `s ↦ P(s⁻¹)`, which is how the statement writes
`Tr(P̂(ρ) P̂(ρ)*)` without choosing an inner product. -/
theorem upper_bound_lemma {G : Type} [Group G] [Fintype G] {ι : Type} [Fintype ι]
    (V : ι → FDRep ℂ G) [∀ i, Simple (V i)]
    (hinj : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    (hsurj : ∀ W : FDRep ℂ G, Simple W → ∃ i, Nonempty (W ≅ V i))
    (P : G → ℝ) (hP : ∑ s, P s = 1) :
    4 * tvDist P (uniform G) ^ 2 ≤
      ∑ i ∈ Finset.univ.filter (fun i => ∃ g, (V i).ρ g ≠ 1),
        (Module.finrank ℂ (V i) : ℝ) *
          (LinearMap.trace ℂ (V i)
            (fourier (V i).ρ (fun s => (P s : ℂ)) *
              fourier (V i).ρ (fun s => (P s⁻¹ : ℂ)))).re := by
  set N : ℝ := (Fintype.card G : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set f : G → ℝ := fun x => P x - N⁻¹ with hf
  have h1 : 4 * tvDist P (uniform G) ^ 2 = (∑ x, |f x|) ^ 2 := by
    simp only [tvDist, uniform, hf, hN]; ring
  have h2 : (∑ x, |f x|) ^ 2 ≤ N * ∑ x, f x ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun x => |f x|)
    simpa [sq_abs, hN] using this
  have hsumf : ∑ x, f x = 0 := by
    simp only [hf, Finset.sum_sub_distrib, hP, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← hN, mul_inv_cancel₀ hNpos.ne', sub_self]
  -- Plancherel for `f`, as a real identity.
  have hpl := MathlibExt.RepresentationTheory.FourierPlancherel.plancherel V hinj hsurj
    (fun s => (f s : ℂ))
  have hre := congrArg Complex.re hpl
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Complex.conj_ofReal] at hre
  rw [show ((Fintype.card G : ℂ))⁻¹ = ((N⁻¹ : ℝ) : ℂ) by push_cast [hN]; rfl, Complex.re_ofReal_mul,
    Complex.re_sum] at hre
  have hterm : ∀ i, ((Module.finrank ℂ (V i) : ℂ) *
      LinearMap.trace ℂ (V i) (fourier (V i).ρ (fun s => (f s : ℂ)) *
        fourier (V i).ρ (fun s => (f s⁻¹ : ℂ)))).re =
      if ∃ g, (V i).ρ g ≠ 1 then (Module.finrank ℂ (V i) : ℝ) *
        (LinearMap.trace ℂ (V i) (fourier (V i).ρ (fun s => (P s : ℂ)) *
          fourier (V i).ρ (fun s => (P s⁻¹ : ℂ)))).re else 0 := fun i => by
    have hsub : ∀ Q : G → ℝ, fourier (V i).ρ (fun s => ((Q s - N⁻¹ : ℝ) : ℂ)) =
        fourier (V i).ρ (fun s => (Q s : ℂ)) -
          fourier (V i).ρ (fun _ => ((Fintype.card G : ℂ))⁻¹) := fun Q => by
      simp only [fourier, Complex.ofReal_sub, Complex.ofReal_inv, sub_smul,
        Finset.sum_sub_distrib, hN, Complex.ofReal_natCast]
    split_ifs with hnt
    · have := BurnsidePaqb.irreducible_of_simple_fdrep G (V i)
      have h0 := fourier_uniform_eq_zero (V i).ρ hnt
      simp only [hf]
      rw [hsub P, hsub (fun s => P s⁻¹), h0, sub_zero, sub_zero]
      simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    · push Not at hnt
      have hz : fourier (V i).ρ (fun s => (f s : ℂ)) = 0 := by
        simp only [fourier, hnt, ← Finset.sum_smul]
        rw [show (∑ s, (f s : ℂ)) = 0 by exact_mod_cast hsumf, zero_smul]
      rw [hz, zero_mul, map_zero, mul_zero, Complex.zero_re]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_filter] at hre
  rw [h1]
  refine h2.trans (le_of_eq ?_)
  rw [hre, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]

/-- **The random-transposition measure is a probability.** For `n ≥ 1`, `∑_σ T(σ) = 1`:
`1/n + (2/n²) C(n, 2) = 1` (Diaconis and Shahshahani 1981, (1.1)). -/
theorem sum_randomTransposition (n : ℕ) [NeZero n] :
    ∑ σ, randomTransposition n σ = 1 := by
  classical
  have hn : 1 ≤ n := NeZero.one_le
  have hpt : ∀ σ : Equiv.Perm (Fin n), randomTransposition n σ =
      (if σ = 1 then 1 / (n : ℝ) else 0) + (if σ.IsSwap then 2 / (n : ℝ) ^ 2 else 0) :=
    fun σ => by
      by_cases h1 : σ = 1
      · subst h1
        have : ¬ (1 : Equiv.Perm (Fin n)).IsSwap := fun h => by
          simpa using Equiv.Perm.card_support_eq_two.mpr h
        simp [randomTransposition, this]
      · simp [randomTransposition, h1]
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rcases Nat.lt_or_ge n 2 with h | h
  · have hn1 : n = 1 := by omega
    subst hn1
    have h1s : ¬ (1 : Equiv.Perm (Fin 1)).IsSwap := fun h => by
      simpa using Equiv.Perm.card_support_eq_two.mpr h
    simp [h1s]
  · have hc := two_mul_card_isSwap n h
    have hc' : ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ.IsSwap).card : ℝ) =
        n * (n - 1) / 2 := by
      rw [eq_div_iff two_ne_zero, mul_comm]
      exact_mod_cast (by rw [hc]; push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring :
        ((2 * (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ.IsSwap).card : ℕ) : ℝ) =
          (n : ℝ) * (n - 1))
    rw [hc']
    field_simp
    ring

/-- The random-transposition measure is invariant under inversion. -/
theorem randomTransposition_inv (n : ℕ) [NeZero n] (σ : Equiv.Perm (Fin n)) :
    randomTransposition n σ⁻¹ = randomTransposition n σ := by
  have h2 : σ⁻¹.IsSwap ↔ σ.IsSwap := by
    rw [← Equiv.Perm.card_support_eq_two, ← Equiv.Perm.card_support_eq_two,
      Equiv.Perm.support_inv]
  unfold randomTransposition
  simp only [inv_eq_one]
  by_cases h : σ.IsSwap <;> simp [h, h2]

section EndpointLaw

open Equiv
open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup (sum_conv)

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem swap_eq_swap_iff {a b i j : Fin n} (hab : a ≠ b) :
    swap i j = swap a b ↔ (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  constructor
  · intro h
    have ha := DFunLike.congr_fun h a
    have hb := DFunLike.congr_fun h b
    simp only [swap_apply_def] at ha hb
    grind
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact swap_comm _ _

/-- Sampling two independent uniform endpoints and interchanging them gives the
random-transposition measure, including the identity step when the endpoints agree. -/
theorem randomTransposition_eq_expect (σ : Equiv.Perm (Fin n)) :
    randomTransposition n σ =
      𝔼 i : Fin n, 𝔼 j : Fin n, if swap i j = σ then (1 : ℝ) else 0 := by
  classical
  by_cases h : σ = 1
  · subst σ
    simp [randomTransposition, swap_eq_one_iff]
  by_cases hs : σ.IsSwap
  · obtain ⟨a, b, hab, rfl⟩ := hs
    have hsplit (i j : Fin n) :
        (if swap i j = swap a b then (1 : ℝ) else 0) =
          (if i = a then (if j = b then 1 else 0) else 0) +
          (if i = b then (if j = a then 1 else 0) else 0) := by
      simp only [swap_eq_swap_iff hab]
      split_ifs <;> grind
    simp_rw [hsplit, Fintype.expect_eq_sum_div_card, Finset.sum_add_distrib,
      Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
    simp [randomTransposition, h, Perm.swap_isSwap_iff, hab, add_div, ite_div,
      Finset.sum_add_distrib]
    ring
  · have hne (i j : Fin n) : swap i j ≠ σ := by
      rintro rfl
      by_cases hij : i = j
      · exact h (swap_eq_one_iff.mpr hij)
      · exact hs (Perm.swap_isSwap_iff.mpr hij)
    simp [randomTransposition, h, hs, hne]

/-- Every convolution power of the random-transposition measure is nonnegative. -/
theorem randomTransposition_convPow_nonneg (k : ℕ) (σ : Equiv.Perm (Fin n)) :
    0 ≤ convPow (randomTransposition n) k σ := by
  induction k generalizing σ with
  | zero => simp [convPow]; split <;> norm_num
  | succ k ih =>
    apply Finset.sum_nonneg
    intro τ _
    apply mul_nonneg _ (ih τ)
    unfold randomTransposition
    split_ifs <;> positivity

/-- Every convolution power of the random-transposition measure has total mass one. -/
theorem sum_randomTransposition_convPow (k : ℕ) :
    ∑ σ, convPow (randomTransposition n) k σ = 1 := by
  induction k with
  | zero => simp [convPow]
  | succ k ih => rw [convPow, sum_conv, sum_randomTransposition, one_mul]; exact ih

end EndpointLaw

open Classical in
/-- **Upper bound for random transpositions.** Let `V : ι → FDRep ℂ Sₙ` be a complete set of
irreducible complex representations of `Sₙ`, of dimensions `d_i` and characters `χ_i`, and let `τ`
be a transposition. Then for every `k`,
`4 ‖T^{*k} - U‖²_TV ≤ ∑_i d_i² (1/n + ((n-1)/n) χ_i(τ)/d_i)^{2k}` (real part), the sum running over
the non-trivial irreducible representations (Diaconis and Shahshahani 1981, Lemma 14, equation
(3.1), stated there for the `ℓ¹` norm `‖·‖ = 2 ‖·‖_TV`). The proof is theirs: the upper bound
lemma combined with Corollary 1. Section 3 of the paper then estimates the sum with Frobenius's
formula for `χ_i(τ)/d_i`. -/
theorem four_mul_tvDist_randomTransposition_sq_le {n : ℕ} [NeZero n] {ι : Type} [Fintype ι]
    (V : ι → FDRep ℂ (Equiv.Perm (Fin n))) [∀ i, Simple (V i)]
    (hinj : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    (hsurj : ∀ W : FDRep ℂ (Equiv.Perm (Fin n)), Simple W → ∃ i, Nonempty (W ≅ V i))
    (τ : Equiv.Perm (Fin n)) (hτ : τ.IsSwap) (k : ℕ) :
    4 * tvDist (convPow (randomTransposition n) k) (uniform (Equiv.Perm (Fin n))) ^ 2 ≤
      ∑ i ∈ Finset.univ.filter (fun i => ∃ g, (V i).ρ g ≠ 1),
        (Module.finrank ℂ (V i) : ℝ) ^ 2 *
          (((1 : ℂ) / n + ((n : ℂ) - 1) / n *
            ((V i).character τ / Module.finrank ℂ (V i))) ^ (2 * k)).re := by
  have hn : 1 ≤ n := by
    have h2 := Equiv.Perm.card_support_eq_two.mpr hτ
    have := Finset.card_le_univ τ.support
    simp only [Fintype.card_fin] at this
    omega
  refine (upper_bound_lemma V hinj hsurj _ (sum_randomTransposition_convPow k)).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  have := BurnsidePaqb.irreducible_of_simple_fdrep (Equiv.Perm (Fin n)) (V i)
  set c : ℂ := (1 : ℂ) / n + ((n : ℂ) - 1) / n *
    ((V i).character τ / Module.finrank ℂ (V i)) with hc
  have hT : fourier (V i).ρ (fun σ => (randomTransposition n σ : ℂ)) = c • 1 :=
    fourier_randomTransposition (V i).ρ τ hτ
  have hcast : ∀ m (s : Equiv.Perm (Fin n)), ((convPow (randomTransposition n) m s : ℝ) : ℂ) =
      convPow (fun σ => (randomTransposition n σ : ℂ)) m s := fun m s =>
    MathlibExt.RepresentationTheory.FourierTransformFiniteGroup.map_convPow Complex.ofRealHom _ m s
  have h1 : fourier (V i).ρ (fun s => ((convPow (randomTransposition n) k s : ℝ) : ℂ)) =
      c ^ k • 1 := by
    simp only [hcast, MathlibExt.RepresentationTheory.FourierTransformFiniteGroup.fourier_convPow,
      hT, smul_pow, one_pow]
  have h2 : fourier (V i).ρ (fun s => ((convPow (randomTransposition n) k s⁻¹ : ℝ) : ℂ)) =
      c ^ k • 1 := by
    simp only [hcast,
      MathlibExt.RepresentationTheory.FourierTransformFiniteGroup.fourier_convPow_comp_inv,
      randomTransposition_inv, hT, smul_pow, one_pow]
  rw [h1, h2, smul_mul_smul_comm, one_mul, map_smul, LinearMap.trace_one, smul_eq_mul, ← pow_add,
    ← two_mul]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
  ring

end UpperBoundLemma

end MathlibExt.Probability.RandomWalkFiniteGroup
