/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Fintype.Pi
import MathlibExt.Analysis.Convex.BrouwerFixedPoint

/-!
# Existence of a mixed Nash equilibrium

Every finite game in which every player has at least one action has a mixed-strategy Nash
equilibrium: a profile of independent probability vectors from which no player gains by
switching to another mixed strategy.

Mixed profiles are families of probability vectors `σ i : A i → ℝ`, and expected payoffs weight
each pure profile by the product of its probabilities. The proof applies Brouwer's theorem to
Nash's map, which shifts probability toward pure actions that beat the current payoff.
`exists_isMixedNash_of_brouwer` takes Brouwer's theorem on the set of mixed profiles as a
hypothesis; `exists_isMixedNash` discharges it with `BrouwerFixedPoint.exists_fixedPoint`.

## Main results

* `exists_isMixedNash`: Nash's existence theorem.

## References

* J. Nash, *Non-cooperative games*, Ann. of Math. 54 (1951), 286–295.
* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Proposition 8.D.2.
-/

@[expose] public section

namespace MathlibExt.GameTheory.MixedNashExistence

/-- Mixed-strategy profiles of a finite game: a family `σ i : A i → ℝ` of probability vectors,
one per player, so `σ i a` is the probability that player `i` plays action `a`. -/
def MixedProfile {ι : Type*} (A : ι → Type*) [∀ i, Fintype (A i)] : Set (∀ i, A i → ℝ) :=
  {σ | ∀ i, (∀ a, 0 ≤ σ i a) ∧ ∑ a, σ i a = 1}

/-- Expected payoff of player `i` when players mix independently according to `σ`: the payoff
`u i a` of each pure profile `a` is weighted by `∏ j, σ j (a j)`. -/
def expectedPayoff {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ) (σ : ∀ i, A i → ℝ) (i : ι) : ℝ :=
  ∑ a : (∀ j, A j), (∏ j, σ j (a j)) * u i a

/-- A mixed Nash equilibrium of the finite game with payoffs `u`: `σ` is a mixed profile and no
player gains by unilaterally switching to another mixed strategy `τ`. -/
def IsMixedNash {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (u : ι → (∀ i, A i) → ℝ) (σ : ∀ i, A i → ℝ) : Prop :=
  σ ∈ MixedProfile A ∧
    ∀ i, ∀ τ : A i → ℝ, (∀ a, 0 ≤ τ a) → ∑ a, τ a = 1 →
      expectedPayoff u (Function.update σ i τ) i ≤ expectedPayoff u σ i

/-- The set of mixed profiles is compact. -/
theorem isCompact_mixedProfile {ι : Type*} (A : ι → Type*) [∀ i, Fintype (A i)] :
    IsCompact (MixedProfile A) := by
  have hEq : MixedProfile A =
      Set.pi Set.univ (fun i => {f : A i → ℝ | (∀ a, 0 ≤ f a) ∧ ∑ a, f a = 1}) := by
    ext σ
    simp [MixedProfile]
  rw [hEq]
  apply isCompact_univ_pi
  intro i
  have hBox : IsCompact (Set.pi Set.univ (fun _ : A i => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hClosed : IsClosed {f : A i → ℝ | (∀ a, 0 ≤ f a) ∧ ∑ a, f a = 1} := by
    have h1 : IsClosed {f : A i → ℝ | ∀ a, 0 ≤ f a} := by
      have : {f : A i → ℝ | ∀ a, 0 ≤ f a} = ⋂ a, (fun f => f a) ⁻¹' Set.Ici 0 := by
        ext f
        simp
      rw [this]
      exact isClosed_iInter (fun a => IsClosed.preimage (continuous_apply a) isClosed_Ici)
    have hcont : Continuous (fun f : A i → ℝ => ∑ a, f a) :=
      continuous_finsetSum Finset.univ (fun a _ => continuous_apply a)
    have h2 : IsClosed {f : A i → ℝ | ∑ a, f a = 1} :=
      isClosed_eq hcont continuous_const
    have : {f : A i → ℝ | (∀ a, 0 ≤ f a) ∧ ∑ a, f a = 1} =
        {f : A i → ℝ | ∀ a, 0 ≤ f a} ∩ {f : A i → ℝ | ∑ a, f a = 1} := by
      ext f
      simp
    rw [this]
    exact h1.inter h2
  have hSub : {f : A i → ℝ | (∀ a, 0 ≤ f a) ∧ ∑ a, f a = 1} ⊆
      Set.pi Set.univ (fun _ : A i => Set.Icc (0 : ℝ) 1) := by
    intro f hf a _
    obtain ⟨hnn, hsum⟩ := hf
    constructor
    · exact hnn a
    · calc f a ≤ ∑ b, f b :=
            Finset.single_le_sum (fun b _ => hnn b) (Finset.mem_univ a)
        _ = 1 := hsum
  exact hBox.of_isClosed_subset hClosed hSub

/-- The set of mixed profiles is convex. -/
theorem convex_mixedProfile {ι : Type*} (A : ι → Type*) [∀ i, Fintype (A i)] :
    Convex ℝ (MixedProfile A) := by
  intro x hx y hy a b ha hb hab i
  obtain ⟨hxn, hxs⟩ := hx i
  obtain ⟨hyn, hys⟩ := hy i
  constructor
  · intro a0
    change 0 ≤ (a • x + b • y) i a0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hxn a0)) (mul_nonneg hb (hyn a0))
  · change ∑ a0, (a • x + b • y) i a0 = 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hxs, hys, mul_one,
      mul_one, hab]

/-- The set of mixed profiles is nonempty when every player has an action. -/
theorem mixedProfile_nonempty {ι : Type*} (A : ι → Type*) [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)] : (MixedProfile A).Nonempty := by
  refine ⟨fun i _ => ((Fintype.card (A i) : ℝ))⁻¹, fun i => ?_⟩
  have hcard : 0 < (Fintype.card (A i) : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr (inferInstanceAs (Nonempty (A i))))
  constructor
  · intro a
    exact le_of_lt (inv_pos.mpr hcard)
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hcard)]

private theorem expectedPayoff_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)]
    (u : ι → (∀ i, A i) → ℝ) (i : ι) :
    Continuous (fun σ : ∀ i, A i → ℝ => expectedPayoff u σ i) := by
  unfold expectedPayoff
  apply continuous_finsetSum Finset.univ
  intro a _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd Finset.univ
  intro j _
  exact (continuous_apply (a j)).comp (continuous_apply j)

private theorem expectedPayoff_update_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (u : ι → (∀ i, A i) → ℝ) (σ : ∀ i, A i → ℝ) (i : ι) (τ : A i → ℝ) :
    expectedPayoff u (Function.update σ i τ) i =
      ∑ a, τ a * expectedPayoff u (Function.update σ i (Pi.single a 1)) i := by
  unfold expectedPayoff
  have hProd : ∀ p : ∀ j, A j,
      ∏ j, (Function.update σ i τ) j (p j) =
        τ (p i) * ∏ j ∈ Finset.univ.erase i, σ j (p j) := by
    intro p
    have h1 : (Function.update σ i τ) i (p i) = τ (p i) := by simp
    have hEq : (∏ j, (Function.update σ i τ) j (p j)) =
        (Function.update σ i τ) i (p i) *
          ∏ j ∈ Finset.univ.erase i, (Function.update σ i τ) j (p j) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    rw [hEq, h1]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    have : Function.update σ i τ j = σ j := Function.update_of_ne hne τ σ
    rw [this]
  have hProdSingle : ∀ (p : ∀ j, A j) (a : A i),
      ∏ j, (Function.update σ i (Pi.single a (1 : ℝ))) j (p j) =
        (Pi.single a (1 : ℝ) : A i → ℝ) (p i) * ∏ j ∈ Finset.univ.erase i, σ j (p j) := by
    intro p a
    have h1 : (Function.update σ i (Pi.single a (1 : ℝ))) i (p i) =
        (Pi.single a (1 : ℝ) : A i → ℝ) (p i) := by simp
    have hEq : (∏ j, (Function.update σ i (Pi.single a (1 : ℝ))) j (p j)) =
        (Function.update σ i (Pi.single a (1 : ℝ))) i (p i) *
          ∏ j ∈ Finset.univ.erase i, (Function.update σ i (Pi.single a (1 : ℝ))) j (p j) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    rw [hEq, h1]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    have : Function.update σ i (Pi.single a (1 : ℝ)) j = σ j :=
      Function.update_of_ne hne _ σ
    rw [this]
  simp_rw [hProd, hProdSingle]
  have hInner : ∀ p : ∀ j, A j,
      (∑ a, τ a * (((Pi.single a (1 : ℝ) : A i → ℝ) (p i) *
        ∏ j ∈ Finset.univ.erase i, σ j (p j)) * u i p)) =
        (τ (p i) * ∏ j ∈ Finset.univ.erase i, σ j (p j)) * u i p := by
    intro p
    have h1 : ∀ a : A i, τ a * (((Pi.single a (1 : ℝ) : A i → ℝ) (p i) *
        ∏ j ∈ Finset.univ.erase i, σ j (p j)) * u i p) =
        (τ a * (Pi.single a (1 : ℝ) : A i → ℝ) (p i)) *
        ((∏ j ∈ Finset.univ.erase i, σ j (p j)) * u i p) := by
      intro a
      ring
    simp_rw [h1, ← Finset.sum_mul]
    have h2 : (∑ a, τ a * (Pi.single a (1 : ℝ) : A i → ℝ) (p i)) = τ (p i) := by
      have h3 : ∀ a : A i, τ a * (Pi.single a (1 : ℝ) : A i → ℝ) (p i) =
          (if p i = a then τ a else 0) := by
        intro a
        rw [Pi.single_apply]
        split_ifs <;> simp
      simp_rw [h3]
      exact Fintype.sum_ite_eq (p i) τ
    rw [h2]
    ring
  calc (∑ p : ∀ j, A j, (τ (p i) * ∏ j ∈ Finset.univ.erase i, σ j (p j)) * u i p)
      = ∑ p : ∀ j, A j, (∑ a, τ a * (((Pi.single a (1 : ℝ) : A i → ℝ) (p i) *
          ∏ j ∈ Finset.univ.erase i, σ j (p j)) * u i p)) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hInner]
    _ = ∑ a, ∑ p : ∀ j, A j, τ a * (((Pi.single a (1 : ℝ) : A i → ℝ) (p i) *
          ∏ j ∈ Finset.univ.erase i, σ j (p j)) * u i p) := by
        rw [Finset.sum_comm]
    _ = ∑ a, τ a * ∑ p : ∀ j, A j, (((Pi.single a (1 : ℝ) : A i → ℝ) (p i) *
          ∏ j ∈ Finset.univ.erase i, σ j (p j)) * u i p) := by
        simp_rw [Finset.mul_sum]

/-- Nash's theorem, derived from Brouwer's theorem on the set of mixed profiles: every finite
game in which every player has at least one action has a mixed Nash equilibrium. -/
theorem exists_isMixedNash_of_brouwer {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (hB : ∀ g : (∀ i, A i → ℝ) → (∀ i, A i → ℝ), ContinuousOn g (MixedProfile A) →
      Set.MapsTo g (MixedProfile A) (MixedProfile A) → ∃ σ ∈ MixedProfile A, g σ = σ)
    (u : ι → (∀ i, A i) → ℝ) :
    ∃ σ, IsMixedNash u σ := by
  classical
  have hCont : ContinuousOn
      (fun σ : ∀ i, A i → ℝ => fun i a =>
        (σ i a + max 0 (expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i -
          expectedPayoff u σ i)) /
        (1 + ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
          expectedPayoff u σ i)))
      (MixedProfile A) := by
    apply Continuous.continuousOn
    rw [continuous_pi_iff]
    intro i
    rw [continuous_pi_iff]
    intro a
    have hE : Continuous (fun σ : ∀ i, A i → ℝ => expectedPayoff u σ i) :=
      expectedPayoff_continuous u i
    have hV : ∀ b : A i, Continuous (fun σ : ∀ i, A i → ℝ =>
        expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i) := fun b =>
      (expectedPayoff_continuous u i).comp
        (Continuous.update continuous_id i continuous_const)
    have hC : ∀ b : A i, Continuous (fun σ : ∀ i, A i → ℝ =>
        max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
          expectedPayoff u σ i)) := fun b =>
      Continuous.max continuous_const (Continuous.sub (hV b) hE)
    have hS : Continuous (fun σ : ∀ i, A i → ℝ =>
        ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
          expectedPayoff u σ i)) :=
      continuous_finsetSum Finset.univ (fun b _ => hC b)
    have hEval : Continuous (fun σ : ∀ i, A i → ℝ => σ i a) :=
      (continuous_apply a).comp (continuous_apply i)
    have hNum : Continuous (fun σ : ∀ i, A i → ℝ =>
        σ i a + max 0 (expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i -
          expectedPayoff u σ i)) :=
      Continuous.add hEval (hC a)
    have hDen : Continuous (fun σ : ∀ i, A i → ℝ =>
        (1 + ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
          expectedPayoff u σ i))) :=
      Continuous.add continuous_const hS
    have hNe : ∀ σ : ∀ i, A i → ℝ,
        (1 + ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
          expectedPayoff u σ i)) ≠ 0 := by
      intro σ
      have hSnn : 0 ≤ ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
          expectedPayoff u σ i) :=
        Finset.sum_nonneg (fun b _ => le_max_left _ _)
      have : (0 : ℝ) < 1 + ∑ b,
          max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
          expectedPayoff u σ i) := by linarith
      exact ne_of_gt this
    exact hNum.div hDen hNe
  have hMaps : Set.MapsTo
      (fun σ : ∀ i, A i → ℝ => fun i a =>
        (σ i a + max 0 (expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i -
          expectedPayoff u σ i)) /
        (1 + ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
          expectedPayoff u σ i)))
      (MixedProfile A) (MixedProfile A) := by
    intro σ hσ i
    obtain ⟨hnn, hsum⟩ := hσ i
    have hSnn : 0 ≤ ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
        expectedPayoff u σ i) :=
      Finset.sum_nonneg (fun b _ => le_max_left _ _)
    have hDpos : (0 : ℝ) < 1 + ∑ b,
        max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
        expectedPayoff u σ i) := by linarith
    have hDne : (1 + ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
        expectedPayoff u σ i)) ≠ 0 := ne_of_gt hDpos
    constructor
    · intro a
      apply div_nonneg _ (le_of_lt hDpos)
      apply add_nonneg (hnn a) (le_max_left _ _)
    · have hSumEq : (∑ a, ((σ i a +
        max 0 (expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i -
          expectedPayoff u σ i)) /
        (1 + ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
          expectedPayoff u σ i)))) =
        (∑ a, (σ i a + max 0 (expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i -
          expectedPayoff u σ i))) /
        (1 + ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
          expectedPayoff u σ i)) := by
        simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      rw [hSumEq, Finset.sum_add_distrib, hsum, div_self hDne]
  obtain ⟨σ, hσmem, hσfix⟩ := hB _ hCont hMaps
  refine ⟨σ, hσmem, ?_⟩
  intro i τ hτnn hτsum
  obtain ⟨hσnn, hσsum⟩ := hσmem i
  set E0 : ℝ := expectedPayoff u σ i with hE0
  have hfix : ∀ a : A i,
      (σ i a + max 0 (expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i - E0)) /
        (1 + ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i - E0)) =
        σ i a := by
    intro a
    have := congrFun (congrFun hσfix i) a
    simpa [hE0] using this
  have hSnn : 0 ≤ ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
      E0) :=
    Finset.sum_nonneg (fun b _ => le_max_left _ _)
  have hDpos : (0 : ℝ) < 1 + ∑ b,
      max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i - E0) := by
    linarith
  have hDne : (1 + ∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
      E0)) ≠ 0 :=
    ne_of_gt hDpos
  have hc_eq : ∀ a : A i, max 0 (expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i -
      E0) =
      σ i a * (∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
          E0)) := by
    intro a
    have h1 : σ i a * (1 + ∑ b,
        max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i - E0)) =
        σ i a + max 0 (expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i - E0) := by
      have hfa := hfix a
      have hcon := congrArg (fun x : ℝ => x * (1 + ∑ b,
          max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i - E0))) hfa
      rw [div_mul_cancel₀ _ hDne] at hcon
      exact hcon.symm
    have h2 : σ i a * (1 + ∑ b,
        max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i - E0)) =
        σ i a + σ i a * (∑ b,
            max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i - E0)) := by
      ring
    rw [h2] at h1
    linarith
  have hIdSelf : E0 = ∑ a, σ i a *
      expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i := by
    have hId := expectedPayoff_update_eq u σ i (σ i)
    rw [Function.update_eq_self] at hId
    simpa [hE0] using hId
  have hex : ∃ a : A i, 0 < σ i a := by
    by_contra h
    push Not at h
    have hzero : ∀ a, σ i a = 0 := fun a => le_antisymm (h a) (hσnn a)
    simp [hzero] at hσsum
  have hexLE : ∃ a : A i, 0 < σ i a ∧
      expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i ≤ E0 := by
    by_contra h
    push Not at h
    have hle : ∀ a : A i, σ i a * E0 ≤ σ i a *
        expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i := by
      intro a
      by_cases ha : 0 < σ i a
      · have hlt : E0 < expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i := h a ha
        exact le_of_lt (mul_lt_mul_of_pos_left hlt ha)
      · push Not at ha
        have h0 : σ i a = 0 := le_antisymm ha (hσnn a)
        simp [h0]
    obtain ⟨a0, ha0pos⟩ := hex
    have hlt0 : σ i a0 * E0 < σ i a0 *
        expectedPayoff u (Function.update σ i (Pi.single a0 (1 : ℝ))) i :=
      mul_lt_mul_of_pos_left (h a0 ha0pos) ha0pos
    have hsumlt : ∑ a, σ i a * E0 < ∑ a, σ i a *
        expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i :=
      Finset.sum_lt_sum (fun a _ => hle a) ⟨a0, Finset.mem_univ a0, hlt0⟩
    have hleft : ∑ a, σ i a * E0 = E0 := by
      rw [← Finset.sum_mul, hσsum, one_mul]
    rw [hleft, ← hIdSelf] at hsumlt
    exact lt_irrefl _ hsumlt
  obtain ⟨a0, ha0pos, ha0le⟩ := hexLE
  have hc0 : max 0 (expectedPayoff u (Function.update σ i (Pi.single a0 (1 : ℝ))) i - E0) = 0 := by
    apply max_eq_left
    have : expectedPayoff u (Function.update σ i (Pi.single a0 (1 : ℝ))) i - E0 ≤ 0 :=
      sub_nonpos.mpr ha0le
    linarith
  have hSeq0 : (∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
      E0)) = 0 := by
    have hc0eq := hc_eq a0
    rw [hc0] at hc0eq
    have : σ i a0 * (∑ b, max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i -
        E0)) = 0 :=
      hc0eq.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt ha0pos)
    · exact h
  have hvle : ∀ b : A i, expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i ≤ E0 := by
    intro b
    have hball : ∀ b ∈ Finset.univ,
        max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i - E0) = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => le_max_left (0 : ℝ) _)).mp hSeq0
      simpa using this
    have hb0 := hball b (Finset.mem_univ b)
    have hle : expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i - E0 ≤
        max 0 (expectedPayoff u (Function.update σ i (Pi.single b (1 : ℝ))) i - E0) :=
      le_max_right _ _
    rw [hb0] at hle
    exact sub_nonpos.mp hle
  have hIdτ := expectedPayoff_update_eq u σ i τ
  rw [hIdτ]
  calc ∑ a, τ a * expectedPayoff u (Function.update σ i (Pi.single a (1 : ℝ))) i
      ≤ ∑ a, τ a * E0 := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hvle a) (hτnn a))
    _ = E0 := by rw [← Finset.sum_mul, hτsum, one_mul]
    _ = expectedPayoff u σ i := rfl

end MathlibExt.GameTheory.MixedNashExistence

namespace MathlibExt.GameTheory.MixedNashExistence

/-- Nash's existence theorem: every finite game in which every player has an action
has a mixed-strategy Nash equilibrium, via Brouwer's fixed-point theorem. -/
theorem exists_isMixedNash {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (u : ι → (∀ i, A i) → ℝ) :
    ∃ σ, IsMixedNash u σ := by
  apply exists_isMixedNash_of_brouwer _ u
  intro g hg hmaps
  exact MathlibExt.Analysis.Convex.BrouwerFixedPoint.exists_fixedPoint
    (isCompact_mixedProfile _) (convex_mixedProfile _) (mixedProfile_nonempty _) hg hmaps

end MathlibExt.GameTheory.MixedNashExistence
