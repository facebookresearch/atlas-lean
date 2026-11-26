/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.TensorPower.ShuffleCuts
public import MathlibExt.Combinatorics.Perm.EulerianPolynomialCoefficients
public import Mathlib.Logic.Equiv.Basic

/-!
# Shuffle cuts and descent multiplicities

A weak cut of n is a pair (p,q) with p,q≥0 and p+q=n. A permutation is a (p,q)-shuffle precisely
when every descent boundary lies at position p. Thus cut-indexed shuffles correspond to
permutations together with a compatible cut. For σ ∈ Sₙ with d descents, the number of
compatible cuts is binom(n+1-d,n).

For a commutative ring k and a k-module V, the sum of all signed cut-shuffle operators on V⊗n is
therefore ∑σ binom(n+1-d(σ),n) · sign(σ)ρₙ(σ). For a commutative ℚ-algebra k and n>0, the
multiplicity is also Bₙ,d(σ)(2), where Bₙ,d(X) = (1/n!)∏ⱼ₌₀ⁿ⁻¹(X+j-d).

For these Eulerian descent coefficients, see J.-L. Loday, Cyclic Homology, 2nd ed., §4.5.
-/

@[expose] public section
noncomputable section

open scoped BigOperators TensorProduct

universe u v

namespace TensorPower

/-- The position coordinate of a weak degree cut.

For n ≥ 0, weak cuts (p,q) with p,q≥0 and p+q=n are equivalent to Fin(n+1) by (p,q) ↦ p. The
inverse sends i to (i,n-i), including both empty-block endpoints. -/
def shuffleDegreeCutPosition (n : ℕ) : ShuffleDegreeCut n ≃ Fin (n + 1) where
  toFun z := ⟨z.1.1, by have h := z.2; omega⟩
  invFun i := ⟨(i.val, n - i.val), by have hi := i.isLt; omega⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change n - z.1.1 = z.1.2
      have h := z.2
      omega
  right_inv i := by apply Fin.ext; rfl

/-- A cut containing every descent boundary.

For σ ∈ Sₙ, CompatibleTwoCuts consists of c ∈ Fin(n+1) with descentBoundaries(σ) ⊆ {c}. A
descent σ(j)>σ(j+1) contributes boundary j+1, so σ must be increasing on both sides of c. -/
abbrev CompatibleTwoCuts {n : ℕ} (σ : Equiv.Perm (Fin n)) :=
  {c : Fin (n + 1) // Equiv.Perm.descentBoundaries σ ⊆ {c}}

/-- The descent-boundary criterion for a two-block shuffle.

For p,q≥0 and σ ∈ Sₚ₊ᵩ, σ is increasing separately on the first p and last q input positions
exactly when descentBoundaries(σ) ⊆ {p}. This includes the two cases of an empty block. -/
theorem isShuffle_iff_descentBoundaries_subset (p q : ℕ) (σ : Equiv.Perm (Fin (p + q))) :
    AlgebraicTopology.EilenbergZilber.IsShuffle σ ↔
      Equiv.Perm.descentBoundaries σ ⊆ {⟨p, by omega⟩} := by
  classical
  rw [Equiv.Perm.isShuffle_iff_descents_at_cut]
  constructor
  · intro h c hc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨hj', hd⟩ := (Finset.mem_filter.mp hj).2
    apply Finset.mem_singleton.mpr
    apply Fin.ext
    exact h j hj' hd
  · intro h j hj hd
    have hmem : j.succ ∈ Equiv.Perm.descentBoundaries σ :=
      Finset.mem_map.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hj, hd⟩⟩, rfl⟩
    exact congrArg Fin.val (Finset.mem_singleton.mp (h hmem))

/-- Compatible cuts as singleton Eulerian cut multisets.

For σ ∈ Sₙ, sending c to the singleton multiset {c} identifies CompatibleTwoCuts(σ) with the
one-element Eulerian cut multisets that contain every descent boundary of σ. -/
def compatibleTwoCutsEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    CompatibleTwoCuts σ ≃ Equiv.Perm.CompatibleEulerianCuts σ 1 where
  toFun c := ⟨Sym.oneEquiv c.val, by
    change (Equiv.Perm.descentBoundaries σ).val ≤ ({c.val} : Finset (Fin (n + 1))).val
    exact Finset.val_le_iff.mpr c.property⟩
  invFun c := ⟨Sym.oneEquiv.symm c.val, by
    have hc := c.property
    have he := Sym.oneEquiv.apply_symm_apply c.val
    rw [← he] at hc
    exact Finset.val_le_iff.mp hc⟩
  left_inv c := by apply Subtype.ext; exact Sym.oneEquiv.symm_apply_apply c.val
  right_inv c := by apply Subtype.ext; exact Sym.oneEquiv.apply_symm_apply c.val

/-- The number of compatible cuts of a permutation.

For σ ∈ Sₙ with descent number d, the cardinality of CompatibleTwoCuts(σ) is binom(n+1-d,n).
In positive degree this is n+1 when d=0, one when d=1, and zero when d≥2. -/
theorem card_compatibleTwoCuts {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Fintype.card (CompatibleTwoCuts σ) = (n + 1 - Equiv.Perm.descentNumber σ).choose n := by
  rw [Fintype.card_congr (compatibleTwoCutsEquiv σ), Equiv.Perm.card_compatibleEulerianCuts]

/-- Shuffles of a fixed cut as compatible permutations.

For a weak cut (p,q) of n, identifying Fin(p+q) with Fin n gives an equivalence from
(p,q)-shuffles to permutations σ ∈ Sₙ with descentBoundaries(σ) ⊆ {p}. -/
def shuffleDegreeCutShuffleEquiv {n : ℕ} (z : ShuffleDegreeCut n) :
    AlgebraicTopology.EilenbergZilber.Shuffle z.1.1 z.1.2 ≃
      {σ : Equiv.Perm (Fin n) //
        Equiv.Perm.descentBoundaries σ ⊆ {shuffleDegreeCutPosition n z}} := by
  rcases z with ⟨⟨p, q⟩, h⟩
  subst n
  exact
    { toFun := fun s => ⟨s.perm, (isShuffle_iff_descentBoundaries_subset p q s.perm).mp s.isShuffle⟩
      invFun := fun s => ⟨s.val, (isShuffle_iff_descentBoundaries_subset p q s.val).mpr s.property⟩
      left_inv := fun s => by cases s; rfl
      right_inv := fun s => by cases s; rfl }

/-- The permutation coordinate of the fixed-cut equivalence.

For a weak cut z=(p,q) with p+q=n and a (p,q)-shuffle s, the underlying permutation of its
image is s.perm transported from Fin(p+q) to Fin n along the degree equality. -/
theorem shuffleDegreeCutShuffleEquiv_perm {n : ℕ} (z : ShuffleDegreeCut n)
    (s : AlgebraicTopology.EilenbergZilber.Shuffle z.1.1 z.1.2) :
    (shuffleDegreeCutShuffleEquiv z s).val = (finCongr z.2).permCongr s.perm := by
  rcases z with ⟨⟨p, q⟩, h⟩
  subst n
  simp [shuffleDegreeCutShuffleEquiv, ← Equiv.Perm.one_def]

/-- Interchanging the cut and permutation indices.

For n ≥ 0, pairs (c,σ) with c ∈ Fin(n+1) and descentBoundaries(σ) ⊆ {c} are equivalent to
pairs (σ,c) with c ∈ CompatibleTwoCuts(σ). The equivalence retains both entries. -/
def swapCutPermutation (n : ℕ) :
    (Σ c : Fin (n + 1), {σ : Equiv.Perm (Fin n) // Equiv.Perm.descentBoundaries σ ⊆ {c}}) ≃
      Σ σ : Equiv.Perm (Fin n), CompatibleTwoCuts σ where
  toFun z := ⟨z.2.val, z.1, z.2.property⟩
  invFun z := ⟨z.2.val, z.1, z.2.property⟩
  left_inv _z := rfl
  right_inv _z := rfl

/-- All cut-indexed shuffles as permutations with compatible cuts.

For n ≥ 0, the disjoint union of (p,q)-shuffles over weak cuts p+q=n is equivalent to pairs
(σ,c) with σ ∈ Sₙ and c ∈ CompatibleTwoCuts(σ). -/
def shuffleCutPermutationEquiv (n : ℕ) :
    (Σ z : ShuffleDegreeCut n, AlgebraicTopology.EilenbergZilber.Shuffle z.1.1 z.1.2) ≃
      Σ σ : Equiv.Perm (Fin n), CompatibleTwoCuts σ := by
  let F : Fin (n + 1) → Type := fun c =>
    {σ : Equiv.Perm (Fin n) // Equiv.Perm.descentBoundaries σ ⊆ {c}}
  let fiber : ∀ z : ShuffleDegreeCut n,
      AlgebraicTopology.EilenbergZilber.Shuffle z.1.1 z.1.2 ≃ F (shuffleDegreeCutPosition n z) :=
    fun z => shuffleDegreeCutShuffleEquiv z
  exact (Equiv.sigmaCongr (β₂ := F) (shuffleDegreeCutPosition n) fiber).trans (swapCutPermutation n)

/-- The total-degree permutation in the cut-shuffle equivalence.

For a weak cut p+q=n and a (p,q)-shuffle s, the permutation component of
shuffleCutPermutationEquiv is s.perm transported along Fin(p+q) ≃ Fin n. -/
theorem shuffleCutPermutationEquiv_perm {n : ℕ}
    (z : Σ c : ShuffleDegreeCut n, AlgebraicTopology.EilenbergZilber.Shuffle c.1.1 c.1.2) :
    (shuffleCutPermutationEquiv n z).1 = (finCongr z.1.2).permCongr z.2.perm := by
  change (shuffleDegreeCutShuffleEquiv z.1 z.2).val = _
  exact shuffleDegreeCutShuffleEquiv_perm z.1 z.2

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

/-- The signed permutation sum for a fixed shuffle cut.

For a commutative ring k, a k-module V and a weak cut p+q=n, shuffleCutEnd is ∑s
sign(σₛ)ρₙ(σₛ) on V⊗n, where s ranges over (p,q)-shuffles and σₛ is its permutation
transported to Fin n. -/
theorem shuffleCutEnd_eq_sum_cast {n : ℕ} (z : ShuffleDegreeCut n) :
    shuffleCutEnd (V := V) z =
      ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle z.1.1 z.1.2,
        (((finCongr z.2).permCongr s.perm).sign : ℤ) •
          (PiTensorProduct.reindex k (fun _ : Fin n => V)
            ((finCongr z.2).permCongr s.perm)).toLinearMap := by
  rcases z with ⟨⟨p, q⟩, h⟩
  subst n
  rw [shuffleCutEnd_eq_cast]
  simp only [TensorPower.cast_refl, LinearEquiv.refl_toLinearMap, LinearMap.id_comp]
  unfold signedShuffleEnd
  apply Finset.sum_congr rfl
  intro s _
  simp [AlgebraicTopology.EilenbergZilber.shuffleSignZ,
    AlgebraicTopology.EilenbergZilber.shuffleSign, ← Equiv.Perm.one_def]

/-- The integral descent multiplicities of two-cut convolution.

For a commutative ring k and a k-module V, shuffleConvolutionTwo on V⊗n equals ∑σ∈Sₙ
binom(n+1-d(σ),n) · sign(σ)ρₙ(σ). The binomial coefficient acts by repeated addition and the
sign by an integer scalar. -/
theorem shuffleConvolutionTwo_eq_descent_sum (n : ℕ) :
    shuffleConvolutionTwo (V := V) n =
      ∑ σ : Equiv.Perm (Fin n),
        ((n + 1 - Equiv.Perm.descentNumber σ).choose n) •
          ((σ.sign : ℤ) • (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap) := by
  classical
  unfold shuffleConvolutionTwo
  simp_rw [shuffleCutEnd_eq_sum_cast]
  let F : (Σ z : ShuffleDegreeCut n,
      AlgebraicTopology.EilenbergZilber.Shuffle z.1.1 z.1.2) → Module.End k (TensorPower k n V) :=
    fun z => (((finCongr z.1.2).permCongr z.2.perm).sign : ℤ) •
      (PiTensorProduct.reindex k (fun _ : Fin n => V)
        ((finCongr z.1.2).permCongr z.2.perm)).toLinearMap
  change (∑ z : ShuffleDegreeCut n,
    ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle z.1.1 z.1.2, F ⟨z, s⟩) = _
  rw [← Fintype.sum_sigma F]
  let e := shuffleCutPermutationEquiv n
  rw [← e.symm.sum_comp F]
  have hperm (z : Σ σ : Equiv.Perm (Fin n), CompatibleTwoCuts σ) :
      (finCongr (e.symm z).1.2).permCongr (e.symm z).2.perm = z.1 := by
    have he := congrArg Sigma.fst (e.apply_symm_apply z)
    exact (shuffleCutPermutationEquiv_perm (e.symm z)).symm.trans he
  have hF (z : Σ σ : Equiv.Perm (Fin n), CompatibleTwoCuts σ) :
      F (e.symm z) = (z.1.sign : ℤ) •
        (PiTensorProduct.reindex k (fun _ : Fin n => V) z.1).toLinearMap := by
    dsimp only [F]
    rw [hperm]
  simp_rw [hF]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro σ _
  change (∑ _ : CompatibleTwoCuts σ,
    ((σ.sign : ℤ) • (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap)) = _
  rw [Finset.sum_const, Finset.card_univ, card_compatibleTwoCuts]

/-- The rational polynomial expression of two-cut convolution.

For a commutative ℚ-algebra k, a k-module V and n>0, shuffleConvolutionTwo on V⊗n equals ∑σ
algebraMap(Bₙ,d(σ)(2)) · sign(σ)ρₙ(σ), with Bₙ,d(X) = (1/n!)∏ⱼ₌₀ⁿ⁻¹(X+j-d). -/
theorem shuffleConvolutionTwo_eq_polynomial [Algebra ℚ k] (n : ℕ) (hn : 0 < n) :
    shuffleConvolutionTwo (V := V) n =
      ∑ σ : Equiv.Perm (Fin n),
        algebraMap ℚ k ((Equiv.Perm.descentBinomialPolynomial n
          (Equiv.Perm.descentNumber σ)).eval 2) •
          ((σ.sign : ℤ) • (PiTensorProduct.reindex k (fun _ : Fin n => V) σ).toLinearMap) := by
  classical
  rw [shuffleConvolutionTwo_eq_descent_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have he := Equiv.Perm.descentBinomialPolynomial_eval_succ n
    (Equiv.Perm.descentNumber σ) 1 hn (Equiv.Perm.descentNumber_lt σ hn)
  have he₂ : (Equiv.Perm.descentBinomialPolynomial n (Equiv.Perm.descentNumber σ)).eval (2 : ℚ) =
      (((n + 1 - Equiv.Perm.descentNumber σ).choose n) : ℚ) := by
    simpa only [Nat.cast_one, one_add_one_eq_two] using he
  rw [he₂, map_natCast, Nat.cast_smul_eq_nsmul]

end TensorPower
