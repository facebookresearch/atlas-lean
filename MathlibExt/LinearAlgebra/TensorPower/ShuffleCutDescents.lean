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
# The actual two-cut shuffle count and its rational polynomial value

The source of the finite sum is the actual dependent pair of a weak degree
cut and an original native shuffle. Casting its permutation to the original
total degree and remembering the original cut is a bijection onto
permutations with a compatible cut. A compatible cut is the original
singleton cut multiset containing every descent boundary. Native stars and
bars and the actual descent polynomial then identify the shuffle sum with
the polynomial value at two. No Eulerian or cut formula is a premise.
-/

@[expose] public section
noncomputable section

open scoped BigOperators TensorProduct

universe u v

namespace TensorPower

/-- Every actual weak cut is determined by its original first block length. -/
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

/-- The original cut positions compatible with the original permutation. -/
abbrev CompatibleTwoCuts {n : ℕ} (σ : Equiv.Perm (Fin n)) :=
  {c : Fin (n + 1) // Equiv.Perm.descentBoundaries σ ⊆ {c}}

/-- The original native shuffle criterion is the singleton-boundary condition. -/
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

/-- A compatible singleton cut is exactly a compatible original cut multiset. -/
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

/-- The actual number of compatible original two-cuts is the descent-binomial value. -/
theorem card_compatibleTwoCuts {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Fintype.card (CompatibleTwoCuts σ) = (n + 1 - Equiv.Perm.descentNumber σ).choose n := by
  rw [Fintype.card_congr (compatibleTwoCutsEquiv σ), Equiv.Perm.card_compatibleEulerianCuts]

/-- An actual cut shuffle is a permutation in the original total degree with its original compatible cut. -/
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

/-- The permutation in the cut bijection is the original degree-cast permutation. -/
theorem shuffleDegreeCutShuffleEquiv_perm {n : ℕ} (z : ShuffleDegreeCut n)
    (s : AlgebraicTopology.EilenbergZilber.Shuffle z.1.1 z.1.2) :
    (shuffleDegreeCutShuffleEquiv z s).val = (finCongr z.2).permCongr s.perm := by
  rcases z with ⟨⟨p, q⟩, h⟩
  subst n
  simp [shuffleDegreeCutShuffleEquiv, ← Equiv.Perm.one_def]

/-- The same native cut/permutation pair with the two dependent indices interchanged. -/
def swapCutPermutation (n : ℕ) :
    (Σ c : Fin (n + 1), {σ : Equiv.Perm (Fin n) // Equiv.Perm.descentBoundaries σ ⊆ {c}}) ≃
      Σ σ : Equiv.Perm (Fin n), CompatibleTwoCuts σ where
  toFun z := ⟨z.2.val, z.1, z.2.property⟩
  invFun z := ⟨z.2.val, z.1, z.2.property⟩
  left_inv _z := rfl
  right_inv _z := rfl

/-- The full finite index is genuinely the permutation together with its compatible original cut. -/
def shuffleCutPermutationEquiv (n : ℕ) :
    (Σ z : ShuffleDegreeCut n, AlgebraicTopology.EilenbergZilber.Shuffle z.1.1 z.1.2) ≃
      Σ σ : Equiv.Perm (Fin n), CompatibleTwoCuts σ := by
  let F : Fin (n + 1) → Type := fun c =>
    {σ : Equiv.Perm (Fin n) // Equiv.Perm.descentBoundaries σ ⊆ {c}}
  let fiber : ∀ z : ShuffleDegreeCut n,
      AlgebraicTopology.EilenbergZilber.Shuffle z.1.1 z.1.2 ≃ F (shuffleDegreeCutPosition n z) :=
    fun z => shuffleDegreeCutShuffleEquiv z
  exact (Equiv.sigmaCongr (β₂ := F) (shuffleDegreeCutPosition n) fiber).trans (swapCutPermutation n)

/-- The actual sigma bijection retains its original degree-cast shuffle permutation. -/
theorem shuffleCutPermutationEquiv_perm {n : ℕ}
    (z : Σ c : ShuffleDegreeCut n, AlgebraicTopology.EilenbergZilber.Shuffle c.1.1 c.1.2) :
    (shuffleCutPermutationEquiv n z).1 = (finCongr z.1.2).permCongr z.2.perm := by
  change (shuffleDegreeCutShuffleEquiv z.1 z.2).val = _
  exact shuffleDegreeCutShuffleEquiv_perm z.1 z.2

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

/-- The actual cast cut is the literal signed sum of its original degree-cast permutations. -/
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

/-- The actual full shuffle-cut operation is the literal signed permutation sum with cut multiplicities. -/
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

/-- The two-cut multiplicity is the actual Eulerian polynomial evaluated at two. -/
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
