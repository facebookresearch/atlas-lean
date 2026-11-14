/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings
public import MathlibExt.Analysis.Normed.Algebra.ExponentialLimit
public import MathlibExt.Biology.PopulationGenetics.Coalescent.BlockCounting
public import MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Nat.Choose.Sum

/-!
# Cannings models with heavy-tailed offspring converge to Λ-coalescents

A **Cannings model** (Cannings 1974) of a haploid population of constant size `N` produces each
generation from the previous one by an exchangeable offspring vector `(ν_1, …, ν_N)`,
`∑ ν_i = N`, independently across generations. We encode one generation as the law of its
parent map `f : Fin N → Fin N`, a `PMF` (`CanningsModel`, from `Cannings.lean`, shared with the
Kingman limit `CanningsKingman`), exchangeable in children and in parents; the offspring numbers
are `ν_i = #{c | f c = i}` (`offspring`). Tracing `b` sampled
lineages back one generation gives `b` → (number of distinct parents) lineages: the ancestral
lineage count, with one-generation transition matrix `lineageMatrix n` on `{0, …, n}`.

The time scale is the **coalescence probability** `c_N = E[ν_1 (ν_1 - 1)] / (N - 1)`, the
probability that two lineages share a parent (`coalProb`). Write `q_k` (`mergeProb k`) for the
probability that `k` lineages share a parent; `q_k (N)_k = E[∑_i (ν_i)_k]`
(`mergeProb_mul_descFactorial`), so `q_k / c_N` is the offspring factorial moment
`E[(ν_1)_k] / (N ^ (k - 1) c_N)` up to a factor tending to `1`.

**Möhle–Sagitov conditions for a Λ-coalescent** (`MohleSagitovLambda M Λ`): `c_N → 0`,
`q_k / c_N → ∫ x ^ (k - 2) Λ(dx)` for every `k ≥ 2`, and simultaneous double mergers are
negligible, `doubleMergeProb / c_N → 0`. The measure Λ is thus **determined by the offspring
law**: its moments are the limits of the scaled offspring factorial moments, and it is unique
(`eq_of_mohleSagitovLambda`, by Pitman's uniqueness theorem).

**The heavy-tail condition** (`HeavyTailed`) is `q_3 / c_N → φ_3 > 0`: three lineages merge
at a rate comparable to two, i.e. the pair-coalescence probability does not dominate the
offspring law. Under the Möhle–Sagitov conditions it holds iff `Λ ≠ δ₀`, i.e. Λ has mass away
from `0` (`heavyTailed_iff`), iff the limiting triple-merger rate `λ_{3,3} = ∫ x Λ(dx)` is
positive (`heavyTailed_iff_mergerRate_pos`); then the limit is not Kingman's coalescent
(`blockCountingGenerator_ne_kingman`). Its failure, `φ_3 = 0`, forces `Λ = δ₀`: Kingman's
coalescent is the boundary case (`blockCountingGenerator_dirac_zero`,
`tendsto_lineageMatrix_pow_dirac_zero`).

**Main theorem** (`tendsto_lineageMatrix_pow`, Möhle–Sagitov 2001; Sagitov 1999): under the
Möhle–Sagitov conditions, for every `t ≥ 0`, the `⌊t / c_N⌋`-generation transition matrix of the
ancestral lineage count converges to `exp (t • G_Λ)`, where `G_Λ` is the block-counting generator
of the Λ-coalescent (`LambdaCoalescent.blockCountingGenerator`: `b → b - k + 1` at rate
`(b choose k) λ_{b,k}`, `λ_{b,k} = ∫ x ^ (k - 2) (1 - x) ^ (b - k) Λ(dx)`).

## Proof

For `a < b` and `k = b + 1 - a`, the event "`b` lineages have `a` parents" is the disjoint
union of the single `k`-mergers (one per `k`-subset of the sample) and events containing a
simultaneous double merger, whose probability is at most `b ^ 4 doubleMergeProb` by
exchangeability and a union bound. A single merger of the set `S` differs from "`S` shares a
parent that no other sampled lineage has" by a double merger, and the latter has probability
`∑_m (b - k choose m) (-1) ^ m q_{k+m}` by inclusion–exclusion (`altMergeSum`). Dividing by `c_N`
and expanding `(1 - x) ^ (b - k)` inside Pitman's integral gives
`c_N⁻¹ (Π_N - 1) → G_Λ` entrywise (`tendsto_smul_lineageMatrix_sub_one`; the diagonal follows
from the row sums). The matrix limit then follows from a compound-interest limit in the Banach
algebra of matrices with general time scale `c_N` (`NormedSpace.tendsto_one_add_smul_pow`).
Exchangeability enters only through `sum_law_comp_emb`: any event for the parents of `m` distinct
children has the same probability as for the first `m` children.

## Scope

Only the ancestral lineage count (block-counting process) is treated, with convergence of its
transition matrices at each fixed time; the partition-valued ancestral process and path-space
(Skorokhod) convergence are not. The Möhle–Sagitov conditions are stated through merger
probabilities, which `mergeProb_mul_descFactorial` identifies with offspring factorial moments;
the joint moment `E[(ν_1)_2 (ν_2)_2]` is not rewritten in offspring form. Existence of a Λ with
prescribed moments (Hausdorff's moment problem) is not used: Λ is part of the hypothesis.

## References

* C. Cannings, *The latent roots of certain Markov chains arising in genetics: a new approach,
  I. Haploid models*, Adv. Appl. Probab. 6 (1974), 260–290.
* S. Sagitov, *The general coalescent with asynchronous mergers of ancestral lines*,
  J. Appl. Probab. 36 (1999), 1116–1125.
* M. Möhle, S. Sagitov, *A classification of coalescent processes for haploid exchangeable
  population models*, Ann. Probab. 29 (2001), 1547–1562.
* B. Eldon, J. Wakeley, *Coalescent processes when the distribution of offspring number among
  individuals is highly skewed*, Genetics 172 (2006), 2621–2633.
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsLambda

open Finset

/-! ### Cannings models

The model `Cannings.CanningsModel` and its sampling API (`sampleProb`, `mergeProb`, `coalProb`,
`doubleMergeProb`, `lineageMatrix`, …) are in `Cannings.lean`, shared with `CanningsKingman`.
The names `CanningsLambda.CanningsModel` and `CanningsLambda.CanningsModel.*` remain available
as aliases. -/

export Cannings (CanningsModel)

namespace CanningsModel

export Cannings.CanningsModel (mk law law_comp_perm law_perm_comp offspring sum_toReal_law
  sampleProb mergeProb coalProb doubleMergeProb lineageProb lineageMatrix sampleProb_congr
  sampleProb_of_le sum_law_comp_emb sampleProb_comp_emb sampleProb_nonneg offspring_comp_perm
  offspring_perm_comp)

end CanningsModel

/-! ### Merger patterns of a sample

For the parents `g : Fin b → α` of `b` sampled lineages: `g` is constant on `U`
(`ConstOn`), the lineages in `S` merge and nothing else happens (`IsSingleMerger`), or two
disjoint pairs merge into two different parents (`HasDoubleMerger`). These are deterministic
facts about functions on `Fin b`. -/

section Patterns

variable {b : ℕ} {α : Type*}

/-- The parents of the lineages in `U` coincide. -/
private abbrev ConstOn (g : Fin b → α) (U : Finset (Fin b)) : Prop :=
  ∀ i ∈ U, ∀ j ∈ U, g i = g j

/-- Exactly the lineages in `S` merge: two lineages share a parent iff they are equal or both
lie in `S`. -/
private abbrev IsSingleMerger (g : Fin b → α) (S : Finset (Fin b)) : Prop :=
  ∀ i j, g i = g j ↔ (i = j ∨ (i ∈ S ∧ j ∈ S))

/-- Two disjoint pairs of lineages merge into two different parents. -/
private abbrev HasDoubleMerger (g : Fin b → α) : Prop :=
  ∃ i₁ i₂ i₃ i₄, i₁ ≠ i₂ ∧ i₃ ≠ i₄ ∧ g i₁ = g i₂ ∧ g i₃ = g i₄ ∧ g i₁ ≠ g i₃

/-- The double merger at the lineages `i 0, i 1` and `i 2, i 3`. -/
private abbrev DoublePattern (i : Fin 4 → Fin b) (g : Fin b → α) : Prop :=
  i 0 ≠ i 1 ∧ i 2 ≠ i 3 ∧ (g (i 0) = g (i 1) ∧ g (i 2) = g (i 3) ∧ g (i 0) ≠ g (i 2))

private lemma card_image_of_isSingleMerger [DecidableEq α] {g : Fin b → α} {S : Finset (Fin b)}
    (h : IsSingleMerger g S) (hS : S.Nonempty) : #(univ.image g) = b + 1 - #S := by
  obtain ⟨s₀, hs₀⟩ := hS
  have himg : univ.image g = (insert s₀ Sᶜ).image g := by
    ext v
    simp only [mem_image, mem_univ, true_and, mem_insert, mem_compl]
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hi : i ∈ S
      · exact ⟨s₀, Or.inl rfl, (h s₀ i).2 (Or.inr ⟨hs₀, hi⟩)⟩
      · exact ⟨i, Or.inr hi, rfl⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
  have hinj : Set.InjOn g ↑(insert s₀ Sᶜ) := by
    intro x hx y hy hxy
    simp only [coe_insert, coe_compl, Set.mem_insert_iff, Set.mem_compl_iff, mem_coe] at hx hy
    rcases (h x y).1 hxy with hxy' | ⟨hxS, hyS⟩
    · exact hxy'
    · rw [hx.resolve_right (not_not.2 hxS), hy.resolve_right (not_not.2 hyS)]
  have hSb : #S ≤ b := by simpa using card_le_univ S
  rw [himg, card_image_of_injOn hinj, card_insert_of_notMem (by simpa using hs₀), card_compl,
    Fintype.card_fin]
  omega

private lemma IsSingleMerger.not_hasDoubleMerger {g : Fin b → α} {S : Finset (Fin b)}
    (h : IsSingleMerger g S) : ¬ HasDoubleMerger g := by
  rintro ⟨i₁, i₂, i₃, i₄, h12, h34, hg12, hg34, hg13⟩
  have h1 := ((h i₁ i₂).1 hg12).resolve_left h12
  have h3 := ((h i₃ i₄).1 hg34).resolve_left h34
  exact hg13 ((h i₁ i₃).2 (Or.inr ⟨h1.1, h3.1⟩))

private lemma IsSingleMerger.eq {g : Fin b → α} {S S' : Finset (Fin b)}
    (h : IsSingleMerger g S) (h' : IsSingleMerger g S') (hS : 2 ≤ #S) (hc : #S = #S') :
    S = S' := by
  refine eq_of_subset_of_card_le (fun i hi => ?_) hc.ge
  obtain ⟨j, hj, hji⟩ := exists_mem_ne (by omega : 1 < #S) i
  exact (((h' i j).1 ((h i j).2 (Or.inr ⟨hi, hj⟩))).resolve_left (Ne.symm hji)).1

private lemma exists_isSingleMerger [DecidableEq α] {g : Fin b → α} (hd : ¬ HasDoubleMerger g)
    (ha : #(univ.image g) < b) : ∃ S, IsSingleMerger g S ∧ 2 ≤ #S := by
  obtain ⟨i, j, hij, hg⟩ : ∃ i j, i ≠ j ∧ g i = g j := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective g := fun x y hxy => by
      by_contra hne
      exact hcon x y hne hxy
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin] at ha
    exact lt_irrefl _ ha
  refine ⟨univ.filter fun l => g l = g i, fun l l' => ?_, ?_⟩
  · simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hll'
      by_cases hl : g l = g i
      · exact Or.inr ⟨hl, hll' ▸ hl⟩
      · by_contra hcon
        exact hd ⟨i, j, l, l', hij, fun h => hcon (Or.inl h), hg, hll', fun h => hl h.symm⟩
    · rintro (rfl | ⟨hl, hl'⟩)
      · rfl
      · rw [hl, hl']
  · have hsub : ({i, j} : Finset (Fin b)) ⊆ univ.filter fun l => g l = g i := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hg]
    calc 2 = #({i, j} : Finset (Fin b)) := (card_pair hij).symm
      _ ≤ _ := card_le_card hsub

private lemma IsSingleMerger.constOn {g : Fin b → α} {S : Finset (Fin b)}
    (h : IsSingleMerger g S) : ConstOn g S :=
  fun i hi j hj => (h i j).2 (Or.inr ⟨hi, hj⟩)

private lemma IsSingleMerger.ne_of_mem_compl {g : Fin b → α} {S : Finset (Fin b)}
    (h : IsSingleMerger g S) {s₀ : Fin b} (hs₀ : s₀ ∈ S) : ∀ t ∈ Sᶜ, g t ≠ g s₀ := by
  intro t ht hts
  rcases (h t s₀).1 hts with rfl | ⟨htS, -⟩
  · exact (mem_compl.1 ht) hs₀
  · exact (mem_compl.1 ht) htS

private lemma isSingleMerger_of_constOn {g : Fin b → α} {S : Finset (Fin b)} {s₀ : Fin b}
    (hS : 2 ≤ #S) (hs₀ : s₀ ∈ S) (hc : ConstOn g S) (hout : ∀ t ∈ Sᶜ, g t ≠ g s₀)
    (hd : ¬ HasDoubleMerger g) : IsSingleMerger g S := by
  intro l l'
  constructor
  · intro hll'
    by_cases hl : l ∈ S
    · by_cases hl' : l' ∈ S
      · exact Or.inr ⟨hl, hl'⟩
      · exact absurd (hll'.symm.trans (hc l hl s₀ hs₀)) (hout l' (mem_compl.2 hl'))
    · by_cases hl' : l' ∈ S
      · exact absurd (hll'.trans (hc l' hl' s₀ hs₀)) (hout l (mem_compl.2 hl))
      · left
        by_contra hne
        obtain ⟨s₁, hs₁, hs₁0⟩ := exists_mem_ne (by omega : 1 < #S) s₀
        exact hd ⟨s₁, s₀, l, l', hs₁0, hne, hc s₁ hs₁ s₀ hs₀, hll',
          fun h => hout l (mem_compl.2 hl) (h.symm.trans (hc s₁ hs₁ s₀ hs₀))⟩
  · rintro (rfl | ⟨hl, hl'⟩)
    · rfl
    · exact hc l hl l' hl'

private lemma hasDoubleMerger_iff {g : Fin b → α} :
    HasDoubleMerger g ↔ ∃ i : Fin 4 → Fin b, DoublePattern i g := by
  constructor
  · rintro ⟨i₁, i₂, i₃, i₄, h⟩
    exact ⟨![i₁, i₂, i₃, i₄], h⟩
  · rintro ⟨i, h01, h23, hg⟩
    exact ⟨_, _, _, _, h01, h23, hg⟩

private lemma DoublePattern.injective {i : Fin 4 → Fin b} {g : Fin b → α}
    (h : DoublePattern i g) : Function.Injective i := by
  obtain ⟨h01, h23, hg01, hg23, hg02⟩ := h
  have h02 : i 0 ≠ i 2 := fun e => hg02 (congrArg g e)
  have h03 : i 0 ≠ i 3 := fun e => hg02 (by rw [e, hg23])
  have h12 : i 1 ≠ i 2 := fun e => hg02 (by rw [hg01, e])
  have h13 : i 1 ≠ i 3 := fun e => hg02 (by rw [hg01, e, hg23])
  intro x y hxy
  fin_cases x <;> fin_cases y <;>
    first
    | rfl
    | exact absurd hxy h01 | exact absurd hxy.symm h01
    | exact absurd hxy h02 | exact absurd hxy.symm h02
    | exact absurd hxy h03 | exact absurd hxy.symm h03
    | exact absurd hxy h12 | exact absurd hxy.symm h12
    | exact absurd hxy h13 | exact absurd hxy.symm h13
    | exact absurd hxy h23 | exact absurd hxy.symm h23

/-- **Inclusion–exclusion** for "the lineages in `S` share a parent that no other lineage has":
the indicator is the alternating sum over the sets `J` of outside lineages of the indicator
that `S ∪ J` share a parent. -/
private lemma indicator_eq_sum_powerset [DecidableEq α] (g : Fin b → α) {S : Finset (Fin b)}
    {s₀ : Fin b} (hs₀ : s₀ ∈ S) :
    (if ConstOn g S ∧ ∀ t ∈ Sᶜ, g t ≠ g s₀ then (1 : ℝ) else 0) =
      ∑ J ∈ Sᶜ.powerset, (-1 : ℝ) ^ #J * if ConstOn g (S ∪ J) then 1 else 0 := by
  by_cases hc : ConstOn g S
  · set A := Sᶜ.filter fun t => g t = g s₀ with hA
    have hJ : ∀ J ∈ Sᶜ.powerset, (-1 : ℝ) ^ #J * (if ConstOn g (S ∪ J) then 1 else 0) =
        if J ⊆ A then (-1 : ℝ) ^ #J else 0 := by
      intro J hJ
      rw [mem_powerset] at hJ
      rw [mul_ite, mul_one, mul_zero]
      refine if_congr ⟨fun h t ht => ?_, fun h i hi j hj => ?_⟩ rfl rfl
      · exact mem_filter.2 ⟨hJ ht, h t (mem_union_right _ ht) s₀ (mem_union_left _ hs₀)⟩
      · have key : ∀ l ∈ S ∪ J, g l = g s₀ := fun l hl => by
          rcases mem_union.1 hl with hl | hl
          · exact hc l hl s₀ hs₀
          · exact (mem_filter.1 (h hl)).2
        rw [key i hi, key j hj]
    rw [sum_congr rfl hJ, ← sum_filter,
      show Sᶜ.powerset.filter (· ⊆ A) = A.powerset by
        ext J
        simp only [mem_filter, mem_powerset]
        exact ⟨fun h => h.2, fun h => ⟨h.trans (filter_subset _ _), h⟩⟩]
    have hsum : ∑ J ∈ A.powerset, (-1 : ℝ) ^ #J = if A = ∅ then 1 else 0 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) (sum_powerset_neg_one_pow_card (x := A))
      push_cast at this
      rw [this]
    rw [hsum]
    have hA0 : (ConstOn g S ∧ ∀ t ∈ Sᶜ, g t ≠ g s₀) ↔ A = ∅ := by
      rw [hA, filter_eq_empty_iff]
      exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
    exact if_congr hA0 rfl rfl
  · rw [ite_eq_right fun h => hc h.1]
    refine (sum_eq_zero fun J _ => ?_).symm
    rw [ite_eq_right fun h => hc fun i hi j hj => h i (mem_union_left _ hi) j (mem_union_left _ hj),
      mul_zero]

end Patterns

end MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsLambda

/-! ### One generation: merger probabilities of a sample

The one-generation results are stated in the namespace of the shared model, so that they apply
by dot notation to every `CanningsModel`. -/

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings.CanningsModel

open Finset CanningsLambda

variable {N : ℕ} (M : CanningsModel N)

/-- The alternating sum `∑_{m=0}^{b-k} (b-k choose m) (-1)^m q_{k+m}` of the merger probabilities
`q_j = mergeProb j`: by inclusion–exclusion, the probability that `k` given lineages among `b`
share a parent that none of the other `b - k` lineages has (`sampleProb_inclusionExclusion`).
Divided by `c_N` it converges to Pitman's rate `λ_{b,k} = ∫ x^(k-2) (1-x)^(b-k) Λ(dx)`. -/
def altMergeSum (b k : ℕ) : ℝ :=
  ∑ m ∈ range (b - k + 1), ((b - k).choose m : ℝ) * ((-1) ^ m * M.mergeProb (k + m))

private lemma sampleProb_eq_expect {b : ℕ} (hb : b ≤ N) (E : (Fin b → Fin N) → Prop)
    [DecidablePred E] : M.sampleProb E = M.expect hb fun g => if E g then 1 else 0 :=
  M.sampleProb_of_le E hb

private lemma ind_nonneg (p : Prop) [Decidable p] : (0 : ℝ) ≤ if p then 1 else 0 := by
  split_ifs <;> norm_num

/-- `k` given lineages of a sample share a parent with probability `mergeProb k`. -/
private lemma sampleProb_constOn {b : ℕ} (hb : b ≤ N) (U : Finset (Fin b)) :
    M.sampleProb (fun g : Fin b → Fin N => ConstOn g U) = M.mergeProb #U := by
  set u : Fin #U ↪ Fin b := (U.orderEmbOfFin rfl).toEmbedding with hu
  rw [mergeProb, ← M.sampleProb_comp_emb hb u]
  refine M.sampleProb_congr fun g => ⟨fun h i j =>
    h _ (U.orderEmbOfFin_mem rfl i) _ (U.orderEmbOfFin_mem rfl j), fun h i hi j hj => ?_⟩
  have hr : ∀ x ∈ U, ∃ y, u y = x := fun x hx => by
    have : x ∈ Set.range (U.orderEmbOfFin rfl) := by rw [range_orderEmbOfFin]; exact hx
    exact this
  obtain ⟨i', rfl⟩ := hr i hi
  obtain ⟨j', rfl⟩ := hr j hj
  exact h i' j'

private lemma sampleProb_false {b : ℕ} :
    M.sampleProb (fun _ : Fin b → Fin N => False) = 0 := by
  unfold sampleProb
  split_ifs <;> simp

/-- A double merger at four given lineages has probability at most `doubleMergeProb` (equal if
the four lineages are distinct, `0` otherwise). -/
private lemma sampleProb_doublePattern_le {b : ℕ} (hb : b ≤ N) (i : Fin 4 → Fin b) :
    M.sampleProb (fun g : Fin b → Fin N => DoublePattern i g) ≤ M.doubleMergeProb := by
  by_cases hi : Function.Injective i
  · rw [doubleMergeProb, ← M.sampleProb_comp_emb hb ⟨i, hi⟩]
    refine le_of_eq (M.sampleProb_congr fun g => ?_)
    have h01 : i 0 ≠ i 1 := hi.ne (by decide)
    have h23 : i 2 ≠ i 3 := hi.ne (by decide)
    exact ⟨fun h => h.2.2, fun h => ⟨h01, h23, h⟩⟩
  · rw [M.sampleProb_congr (E' := fun _ => False) fun g => ⟨fun h => hi h.injective, False.elim⟩,
      sampleProb_false]
    exact M.sampleProb_nonneg _

/-- A simultaneous double merger somewhere in a sample of `b` has probability at most
`b ^ 4 * doubleMergeProb` (union bound over the four lineages involved). -/
private lemma sampleProb_hasDoubleMerger_le {b : ℕ} (hb : b ≤ N) :
    M.sampleProb (fun g : Fin b → Fin N => HasDoubleMerger g) ≤
      (b : ℝ) ^ 4 * M.doubleMergeProb := by
  rw [M.sampleProb_eq_expect hb]
  calc M.expect hb (fun g => if HasDoubleMerger g then 1 else 0)
      ≤ M.expect hb (fun g => ∑ i : Fin 4 → Fin b, if DoublePattern i g then 1 else 0) :=
        M.expect_mono fun g => by
          split_ifs with h
          · obtain ⟨i, hi⟩ := hasDoubleMerger_iff.1 h
            calc (1 : ℝ) = if DoublePattern i g then 1 else 0 := (ite_eq_left hi).symm
              _ ≤ _ := single_le_sum (f := fun i => if DoublePattern i g then (1 : ℝ) else 0)
                  (fun j _ => ind_nonneg _) (mem_univ i)
          · exact sum_nonneg fun j _ => ind_nonneg _
    _ = ∑ i : Fin 4 → Fin b, M.sampleProb (fun g => DoublePattern i g) := by
        rw [M.expect_sum]
        exact sum_congr rfl fun i _ => (M.sampleProb_eq_expect hb _).symm
    _ ≤ ∑ _i : Fin 4 → Fin b, M.doubleMergeProb :=
        sum_le_sum fun i _ => M.sampleProb_doublePattern_le hb i
    _ = _ := by simp

/-- **Inclusion–exclusion.** For `s₀ ∈ S`, the probability that the lineages in `S` share a
parent that no other lineage of the sample has is `altMergeSum b #S`. -/
private lemma sampleProb_inclusionExclusion {b : ℕ} (hb : b ≤ N) {S : Finset (Fin b)}
    {s₀ : Fin b} (hs₀ : s₀ ∈ S) :
    M.sampleProb (fun g : Fin b → Fin N => ConstOn g S ∧ ∀ t ∈ Sᶜ, g t ≠ g s₀) =
      M.altMergeSum b #S := by
  rw [M.sampleProb_eq_expect hb]
  simp_rw [indicator_eq_sum_powerset _ hs₀]
  rw [M.expect_sum]
  simp_rw [M.expect_const_mul, ← M.sampleProb_eq_expect hb, M.sampleProb_constOn hb]
  rw [sum_congr rfl fun J hJ => by
    rw [card_union_eq_card_add_card.2
      (disjoint_of_subset_right (mem_powerset.1 hJ) disjoint_compl_right)]]
  rw [sum_powerset_apply_card (fun m => (-1 : ℝ) ^ m * M.mergeProb (#S + m)), card_compl,
    Fintype.card_fin, altMergeSum]
  simp_rw [nsmul_eq_mul]

/-- **One-generation estimate.** For `a < b ≤ N`, with `k = b + 1 - a`, the probability that `b`
lineages have `a` parents is `(b choose k) * altMergeSum b k` (a single `k`-merger) up to an
error of at most `((b choose k) + 1) b ^ 4 doubleMergeProb` (simultaneous mergers). -/
theorem abs_lineageProb_sub_le {b a : ℕ} (hb : b ≤ N) (ha : a < b) :
    |M.lineageProb b a - (b.choose (b + 1 - a) : ℝ) * M.altMergeSum b (b + 1 - a)| ≤
      ((b.choose (b + 1 - a) : ℝ) + 1) * ((b : ℝ) ^ 4 * M.doubleMergeProb) := by
  set k := b + 1 - a with hk
  have hk2 : 2 ≤ k := by omega
  set D := M.sampleProb (fun g : Fin b → Fin N => HasDoubleMerger g) with hD
  have hDle : D ≤ (b : ℝ) ^ 4 * M.doubleMergeProb := M.sampleProb_hasDoubleMerger_le hb
  have hD0 : 0 ≤ D := M.sampleProb_nonneg _
  set 𝒮 := powersetCard k (univ : Finset (Fin b)) with h𝒮
  -- the event "`a` parents" splits into single `k`-mergers and simultaneous mergers
  have h1 : M.lineageProb b a = ∑ S ∈ 𝒮, M.sampleProb (fun g : Fin b → Fin N =>
      IsSingleMerger g S) + M.sampleProb (fun g : Fin b → Fin N =>
        #(univ.image g) = a ∧ HasDoubleMerger g) := by
    rw [lineageProb, M.sampleProb_eq_expect hb, M.sampleProb_eq_expect hb]
    simp_rw [M.sampleProb_eq_expect hb, ← M.expect_sum, ← M.expect_add]
    congr 1
    funext g
    by_cases hd : HasDoubleMerger g
    · rw [sum_eq_zero fun S _ => ite_eq_right fun h => h.not_hasDoubleMerger hd, zero_add]
      exact if_congr ⟨fun h => ⟨h, hd⟩, fun h => h.1⟩ rfl rfl
    · have h0 : (if #(univ.image g) = a ∧ HasDoubleMerger g then (1 : ℝ) else 0) = 0 :=
        ite_eq_right fun h => hd h.2
      rw [h0, add_zero, sum_boole]
      by_cases hga : #(univ.image g) = a
      · rw [ite_eq_left hga]
        obtain ⟨S, hS, hS2⟩ := exists_isSingleMerger hd (by omega)
        have hSb : #S ≤ b := by simpa using card_le_univ S
        have hSk : #S = k := by
          have := card_image_of_isSingleMerger hS (card_pos.1 (by omega))
          omega
        have hmem : S ∈ 𝒮 := mem_powersetCard.2 ⟨subset_univ _, hSk⟩
        have hcard : #{S ∈ 𝒮 | IsSingleMerger g S} = 1 := by
          refine le_antisymm (card_le_one.2 fun S₁ h₁ S₂ h₂ => ?_)
            (card_pos.2 ⟨S, mem_filter.2 ⟨hmem, hS⟩⟩)
          obtain ⟨h₁𝒮, h₁⟩ := mem_filter.1 h₁
          obtain ⟨h₂𝒮, h₂⟩ := mem_filter.1 h₂
          have c₁ := (mem_powersetCard.1 h₁𝒮).2
          have c₂ := (mem_powersetCard.1 h₂𝒮).2
          exact h₁.eq h₂ (by omega) (by omega)
        rw [hcard, Nat.cast_one]
      · rw [ite_eq_right hga]
        refine (Nat.cast_eq_zero.2 (card_eq_zero.2 (filter_eq_empty_iff.2 fun S hS h => ?_))).symm
        have hSk := (mem_powersetCard.1 hS).2
        have := card_image_of_isSingleMerger h (card_pos.1 (by omega))
        exact hga (by omega)
  -- each single merger: inclusion–exclusion up to a simultaneous merger
  have h2 : ∀ S ∈ 𝒮, ∃ e, 0 ≤ e ∧ e ≤ D ∧
      M.sampleProb (fun g : Fin b → Fin N => IsSingleMerger g S) = M.altMergeSum b k - e := by
    intro S hS
    have hSk := (mem_powersetCard.1 hS).2
    obtain ⟨s₀, hs₀⟩ := card_pos.1 (by omega : 0 < #S)
    refine ⟨M.sampleProb (fun g : Fin b → Fin N =>
      (ConstOn g S ∧ ∀ t ∈ Sᶜ, g t ≠ g s₀) ∧ ¬ IsSingleMerger g S), M.sampleProb_nonneg _, ?_, ?_⟩
    · rw [M.sampleProb_eq_expect hb, hD, M.sampleProb_eq_expect hb]
      refine M.expect_mono fun g => ?_
      split_ifs with h h'
      · exact le_rfl
      · exact absurd (by_contra fun hd => h.2 (isSingleMerger_of_constOn (by omega) hs₀ h.1.1
          h.1.2 hd)) h'
      · exact zero_le_one
      · exact le_rfl
    · rw [← hSk, ← M.sampleProb_inclusionExclusion hb hs₀, eq_sub_iff_add_eq,
        M.sampleProb_eq_expect hb, M.sampleProb_eq_expect hb, M.sampleProb_eq_expect hb,
        ← M.expect_add]
      congr 1
      funext g
      by_cases h : IsSingleMerger g S
      · have e1 : (if (ConstOn g S ∧ ∀ t ∈ Sᶜ, g t ≠ g s₀) ∧ ¬ IsSingleMerger g S then (1 : ℝ)
            else 0) = 0 := ite_eq_right fun h' => h'.2 h
        have e2 : (if ConstOn g S ∧ ∀ t ∈ Sᶜ, g t ≠ g s₀ then (1 : ℝ) else 0) = 1 :=
          ite_eq_left ⟨h.constOn, h.ne_of_mem_compl hs₀⟩
        rw [ite_eq_left h, e1, e2, add_zero]
      · rw [ite_eq_right h, zero_add]
        exact if_congr ⟨fun h' => h'.1, fun h' => ⟨h', h⟩⟩ rfl rfl
  choose! e he0 heD hse using h2
  have h3 : M.sampleProb (fun g : Fin b → Fin N => #(univ.image g) = a ∧ HasDoubleMerger g) ≤
      D := by
    rw [M.sampleProb_eq_expect hb, hD, M.sampleProb_eq_expect hb]
    exact M.expect_mono fun g => by
      split_ifs with h h' <;> first | exact le_rfl | exact zero_le_one | exact absurd h.2 h'
  have h30 := M.sampleProb_nonneg (fun g : Fin b → Fin N => #(univ.image g) = a ∧
    HasDoubleMerger g)
  have hcard : (#𝒮 : ℝ) = b.choose k := by
    rw [h𝒮, card_powersetCard, card_univ, Fintype.card_fin]
  have hsum : ∑ S ∈ 𝒮, M.sampleProb (fun g : Fin b → Fin N => IsSingleMerger g S) =
      b.choose k * M.altMergeSum b k - ∑ S ∈ 𝒮, e S := by
    rw [sum_congr rfl hse, sum_sub_distrib, sum_const, nsmul_eq_mul, hcard]
  have he : ∑ S ∈ 𝒮, e S ≤ b.choose k * D := by
    calc ∑ S ∈ 𝒮, e S ≤ ∑ _S ∈ 𝒮, D := sum_le_sum heD
      _ = b.choose k * D := by rw [sum_const, nsmul_eq_mul, hcard]
  have he0' : 0 ≤ ∑ S ∈ 𝒮, e S := sum_nonneg he0
  rw [h1, hsum]
  have hC : (0 : ℝ) ≤ b.choose k := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Offspring moments -/

/-- The embeddings of `Fin k` whose images all have parent `p` are the embeddings into the
offspring of `p`. -/
private def embFiberEquiv (f : Fin N → Fin N) (k : ℕ) (p : Fin N) :
    {e : Fin k ↪ Fin N // ∀ i, f (e i) = p} ≃ (Fin k ↪ {c // f c = p}) where
  toFun e := ⟨fun i => ⟨e.1 i, e.2 i⟩, fun _ _ hij => e.1.injective (congrArg Subtype.val hij)⟩
  invFun e := ⟨e.trans (Function.Embedding.subtype _), fun i => (e i).2⟩
  left_inv _ := Subtype.ext (Function.Embedding.ext fun _ => rfl)
  right_inv _ := Function.Embedding.ext fun _ => rfl

/-- **Merger probabilities are offspring factorial moments**:
`q_k (N)_k = E[∑_i (ν_i)_k]`, where `(x)_k` is the falling factorial. Under exchangeability in
the parents the right side is `N E[(ν_1)_k]`, so `q_k = N E[(ν_1)_k] / (N)_k` and in particular
`c_N = E[ν_1 (ν_1 - 1)] / (N - 1)` (Möhle–Sagitov 2001, §2). -/
theorem mergeProb_mul_descFactorial {k : ℕ} (hk : 1 ≤ k) :
    M.mergeProb k * N.descFactorial k =
      ∑ f, (M.law f).toReal * ∑ i, ((offspring f i).descFactorial k : ℝ) := by
  classical
  have hcount : ∀ f : Fin N → Fin N,
      ((univ.filter fun e : Fin k ↪ Fin N => ∀ i j, f (e i) = f (e j)).card : ℝ) =
        ∑ p, ((offspring f p).descFactorial k : ℝ) := by
    intro f
    rw [card_eq_sum_card_fiberwise (f := fun e : Fin k ↪ Fin N => f (e ⟨0, hk⟩))
      (t := univ) fun _ _ => mem_univ _]
    push_cast
    refine sum_congr rfl fun p _ => ?_
    have hfib : (univ.filter fun e : Fin k ↪ Fin N => ∀ i j, f (e i) = f (e j)).filter
        (fun e => f (e ⟨0, hk⟩) = p) = univ.filter fun e : Fin k ↪ Fin N => ∀ i, f (e i) = p := by
      ext e
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h i => (h.1 i ⟨0, hk⟩).trans h.2, fun h => ⟨fun i j => (h i).trans (h j).symm,
        h _⟩⟩
    rw [hfib, ← Fintype.card_subtype, Fintype.card_congr (embFiberEquiv f k p),
      Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_subtype, offspring]
  have hemb : ∀ e : Fin k ↪ Fin N,
      ∑ f, (M.law f).toReal * (if ∀ i j, (f ∘ e) i = (f ∘ e) j then 1 else 0) =
        M.mergeProb k :=
    fun e => M.sum_law_comp_emb e (fun g : Fin k → Fin N => ∀ i j, g i = g j)
  calc M.mergeProb k * N.descFactorial k
      = ∑ _e : Fin k ↪ Fin N, M.mergeProb k := by
        rw [sum_const, card_univ, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul, mul_comm]
    _ = ∑ e : Fin k ↪ Fin N, ∑ f, (M.law f).toReal *
          (if ∀ i j, (f ∘ e) i = (f ∘ e) j then 1 else 0) := sum_congr rfl fun e _ => (hemb e).symm
    _ = ∑ f, (M.law f).toReal * ((univ.filter fun e : Fin k ↪ Fin N =>
          ∀ i j, f (e i) = f (e j)).card : ℝ) := by
        rw [sum_comm]
        refine sum_congr rfl fun f _ => ?_
        rw [← mul_sum, sum_boole]
        rfl
    _ = _ := sum_congr rfl fun f _ => by rw [hcount]

/-- Lineages are never gained: `b` lineages have at most `b` parents. -/
theorem lineageProb_eq_zero_of_lt {b a : ℕ} (h : b < a) : M.lineageProb b a = 0 := by
  rw [lineageProb, M.sampleProb_congr (E' := fun _ => False) fun g => ⟨fun hg => by
    have := card_image_le (s := (univ : Finset (Fin b))) (f := g)
    rw [card_univ, Fintype.card_fin] at this
    omega, False.elim⟩]
  unfold sampleProb
  split_ifs <;> simp

/-- A nonempty sample has at least one parent. -/
theorem lineageProb_zero {b : ℕ} (hb : 1 ≤ b) : M.lineageProb b 0 = 0 := by
  rw [lineageProb, M.sampleProb_congr (E' := fun _ => False) fun g => ⟨fun hg => by
    have : (univ.image g).Nonempty := (univ_nonempty_iff.2 ⟨⟨0, hb⟩⟩).image g
    rw [← card_pos, hg] at this
    exact lt_irrefl _ this, False.elim⟩]
  unfold sampleProb
  split_ifs <;> simp

/-- The rows of the lineage-count transition matrix sum to `1`. -/
theorem sum_lineageProb {n b : ℕ} (hbn : b ≤ n) (hbN : b ≤ N) :
    ∑ a : Fin (n + 1), M.lineageProb b a = 1 := by
  simp_rw [lineageProb, M.sampleProb_of_le _ hbN]
  rw [sum_comm]
  refine (sum_congr rfl fun f _ => ?_).trans M.sum_toReal_law
  rw [← mul_sum, sum_boole]
  set g := f ∘ Fin.castLE hbN
  have hle : #(univ.image g) ≤ b := by
    simpa using card_image_le (s := (univ : Finset (Fin b))) (f := g)
  have hfil : (univ.filter fun a : Fin (n + 1) => #(univ.image g) = (a : ℕ)) =
      {⟨#(univ.image g), by omega⟩} := by
    ext a
    simp [Fin.ext_iff, eq_comm]
  rw [hfil, card_singleton, Nat.cast_one, mul_one]

end MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings.CanningsModel

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsLambda

open Finset

namespace CanningsModel

export Cannings.CanningsModel (altMergeSum abs_lineageProb_sub_le mergeProb_mul_descFactorial
  lineageProb_eq_zero_of_lt lineageProb_zero sum_lineageProb)

end CanningsModel

/-! ### The Möhle–Sagitov conditions and the Λ-coalescent limit -/

open MeasureTheory unitInterval CanningsModel

section Limit

variable (M : (N : ℕ) → CanningsModel N) (Λ : Measure I) [IsFiniteMeasure Λ]

/-- The **Möhle–Sagitov conditions for a Λ-coalescent limit** of a sequence of Cannings models
(`M N` has population size `N`), with Λ a finite measure on `[0, 1]`:

* the coalescence probability `c_N` is eventually positive and tends to `0`;
* for every `k ≥ 2`, the probability `q_k` that `k` lineages merge in one generation satisfies
  `q_k / c_N → ∫ x ^ (k - 2) Λ(dx)`; by `mergeProb_mul_descFactorial` this is the offspring
  condition `E[(ν_1)_k] / (N ^ (k - 1) c_N) → ∫ x ^ (k - 2) Λ(dx)` of Möhle–Sagitov (2001);
* simultaneous mergers are negligible: `doubleMergeProb / c_N → 0`, equivalently
  `E[(ν_1)_2 (ν_2)_2] / (N ^ 2 c_N) → 0`.

The limits `φ_k = lim q_k / c_N` are the moments of Λ, so Λ is determined by the model
(`eq_of_mohleSagitovLambda`); `k = 2` forces Λ to be a probability measure. -/
structure MohleSagitovLambda : Prop where
  eventually_coalProb_pos : ∀ᶠ N in atTop, 0 < (M N).coalProb
  tendsto_coalProb : Tendsto (fun N => (M N).coalProb) atTop (𝓝 0)
  tendsto_mergeProb_div : ∀ k, 2 ≤ k →
    Tendsto (fun N => (M N).mergeProb k / (M N).coalProb) atTop (𝓝 (∫ x, (x : ℝ) ^ (k - 2) ∂Λ))
  tendsto_doubleMergeProb_div :
    Tendsto (fun N => (M N).doubleMergeProb / (M N).coalProb) atTop (𝓝 0)

/-- The **heavy-tail condition**: a triple merger is not negligible against a pair merger,
`q_3 / c_N → φ_3 > 0`; in offspring terms `E[(ν_1)_3] / (N ^ 2 c_N) → φ_3 > 0`, i.e. the offspring
law puts enough mass on families of size of order `N`. Under the Möhle–Sagitov conditions this
says exactly that Λ is not Kingman's `δ₀` (`heavyTailed_iff`); its failure (`φ_3 = 0`) is
Möhle's condition for the Kingman limit. -/
def HeavyTailed : Prop :=
  ∃ φ, 0 < φ ∧ Tendsto (fun N => (M N).mergeProb 3 / (M N).coalProb) atTop (𝓝 φ)

variable {M Λ}

private lemma integrable_pow (j : ℕ) : Integrable (fun x : I => (x : ℝ) ^ j) Λ := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg x.2.1 _)]
  exact pow_le_one₀ x.2.1 x.2.2

/-- Pitman's rate expanded in the moments of Λ:
`λ_{b,k} = ∑_m (b-k choose m) (-1)^m ∫ x ^ (k+m-2) Λ(dx)`. -/
private lemma mergerRate_eq_sum {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b) :
    LambdaCoalescent.mergerRate Λ b k = ∑ m ∈ range (b - k + 1),
      ((b - k).choose m : ℝ) * ((-1) ^ m * ∫ x, (x : ℝ) ^ (k + m - 2) ∂Λ) := by
  rw [LambdaCoalescent.mergerRate_of_le Λ hk hkb]
  have hpoly : ∀ x : ℝ, x ^ (k - 2) * (1 - x) ^ (b - k) =
      ∑ m ∈ range (b - k + 1), ((b - k).choose m : ℝ) * ((-1) ^ m * x ^ (k + m - 2)) := by
    intro x
    rw [sub_eq_add_neg, add_comm, add_pow, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [show k + m - 2 = (k - 2) + m by omega, pow_add, neg_pow, one_pow, mul_one]
    ring
  simp_rw [hpoly]
  rw [integral_finsetSum _ fun m _ => ((integrable_pow _).const_mul _).const_mul _]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_const_mul, integral_const_mul]

private lemma tendsto_altMergeSum_div (h : MohleSagitovLambda M Λ) {b k : ℕ} (hk : 2 ≤ k)
    (hkb : k ≤ b) : Tendsto (fun N => (M N).altMergeSum b k / (M N).coalProb) atTop
      (𝓝 (LambdaCoalescent.mergerRate Λ b k)) := by
  rw [mergerRate_eq_sum hk hkb]
  simp_rw [altMergeSum, sum_div]
  refine tendsto_finsetSum _ fun m _ => ?_
  have := ((h.tendsto_mergeProb_div (k + m) (by omega)).const_mul ((-1 : ℝ) ^ m)).const_mul
    ((b - k).choose m : ℝ)
  refine this.congr fun N => ?_
  ring

/-- **The one-generation limit.** For `a < b`, the probability that `b` lineages have `a`
parents, divided by `c_N`, tends to the Λ-coalescent jump rate
`(b choose k) λ_{b,k}` with `k = b + 1 - a`. -/
theorem tendsto_lineageProb_div (h : MohleSagitovLambda M Λ) {b a : ℕ} (ha : a < b) :
    Tendsto (fun N => (M N).lineageProb b a / (M N).coalProb) atTop
      (𝓝 ((b.choose (b + 1 - a) : ℝ) * LambdaCoalescent.mergerRate Λ b (b + 1 - a))) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    refine tendsto_const_nhds.congr fun N => ?_
    rw [lineageProb_zero _ (by omega), zero_div]
  set k := b + 1 - a with hk
  set C : ℝ := ((b.choose k : ℕ) : ℝ) with hC
  have hT : Tendsto (fun N => C * ((M N).altMergeSum b k / (M N).coalProb)) atTop
      (𝓝 (C * LambdaCoalescent.mergerRate Λ b k)) :=
    (tendsto_altMergeSum_div h (by omega) (by omega)).const_mul C
  have hE : Tendsto (fun N => ((M N).lineageProb b a - C * (M N).altMergeSum b k) /
      (M N).coalProb) atTop (𝓝 0) := by
    have hbd := (h.tendsto_doubleMergeProb_div.const_mul ((C + 1) * (b : ℝ) ^ 4))
    rw [mul_zero] at hbd
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [h.eventually_coalProb_pos, eventually_ge_atTop b] with N hc hbN
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hc, div_le_iff₀ hc]
    calc |(M N).lineageProb b a - C * (M N).altMergeSum b k|
        ≤ (C + 1) * ((b : ℝ) ^ 4 * (M N).doubleMergeProb) := (M N).abs_lineageProb_sub_le hbN ha
      _ = _ := by field_simp
  have hTE := hT.add hE
  rw [add_zero] at hTE
  refine hTE.congr fun N => ?_
  ring

/-- **Generator convergence.** `c_N⁻¹ • (Π_N - 1)` converges entrywise to the generator of the
Λ-coalescent's block-counting process, where `Π_N` is the one-generation transition matrix of
the ancestral lineage count. -/
theorem tendsto_smul_lineageMatrix_sub_one (h : MohleSagitovLambda M Λ) (n : ℕ) :
    Tendsto (fun N => (M N).coalProb⁻¹ • ((M N).lineageMatrix n - 1)) atTop
      (𝓝 (LambdaCoalescent.blockCountingGenerator Λ n)) := by
  set G := LambdaCoalescent.blockCountingGenerator Λ n with hG
  have hoff : ∀ i j : Fin (n + 1), i ≠ j →
      Tendsto (fun N => (M N).lineageProb i j / (M N).coalProb) atTop (𝓝 (G i j)) := by
    intro i j hij
    have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hij' with hlt | hlt
    · have hG0 : G i j = 0 := by
        simp only [hG, LambdaCoalescent.blockCountingGenerator, hij, ite_false]
        exact ite_eq_right (by omega)
      rw [hG0]
      refine tendsto_const_nhds.congr fun N => ?_
      rw [lineageProb_eq_zero_of_lt _ hlt, zero_div]
    · have hGij : G i j = ((i : ℕ).choose (i + 1 - j) : ℝ) *
          LambdaCoalescent.mergerRate Λ i (i + 1 - j) := by
        simp only [hG, LambdaCoalescent.blockCountingGenerator, hij, ite_false]
        exact ite_eq_left hlt
      rw [hGij]
      exact tendsto_lineageProb_div h hlt
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  change Tendsto (fun N => (M N).coalProb⁻¹ * ((M N).lineageProb i j -
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j)) atTop (𝓝 (G i j))
  by_cases hij : i = j
  · subst hij
    have hrow : ∑ a, G i a = 0 :=
      (LambdaCoalescent.isRateMatrix_blockCountingGenerator Λ n).sum_row i
    rw [← add_sum_erase _ _ (mem_univ i)] at hrow
    rw [show G i i = -∑ a ∈ univ.erase i, G i a by linarith]
    have hlim := (tendsto_finsetSum (univ.erase i) fun a ha =>
      hoff i a (ne_of_mem_erase ha).symm).neg
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop n] with N hN
    have hsum := (M N).sum_lineageProb (n := n) (b := i) (by omega) (by omega)
    rw [← add_sum_erase _ _ (mem_univ i)] at hsum
    have hd : (M N).lineageProb i i - 1 = -∑ a ∈ univ.erase i, (M N).lineageProb i a := by
      linarith
    rw [Matrix.one_apply_eq, hd, ← sum_div]
    ring
  · refine (hoff i j hij).congr fun N => ?_
    rw [Matrix.one_apply_ne hij]
    simp [div_eq_inv_mul]

/-- `⌊t / c⌋ c → t` as `c → 0⁺`. -/
private lemma tendsto_floor_div_mul {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hpos : ∀ᶠ N in atTop, 0 < c N) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun N => (⌊t / c N⌋₊ : ℝ) * c N) atTop (𝓝 t) := by
  have hlow : Tendsto (fun N => t - c N) atTop (𝓝 t) := by simpa using hc.const_sub t
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hpos] with N hN
    have := Nat.lt_floor_add_one (t / c N)
    rw [div_lt_iff₀ hN] at this
    nlinarith
  · filter_upwards [hpos] with N hN
    have := Nat.floor_le (div_nonneg ht hN.le)
    rwa [le_div_iff₀ hN] at this

/-- **Möhle–Sagitov: convergence of a Cannings model to the Λ-coalescent.** Under the
Möhle–Sagitov conditions, for every `t ≥ 0` the `⌊t / c_N⌋`-generation transition matrix of the
ancestral lineage count of a sample of at most `n` converges, as `N → ∞`, to the time-`t`
transition matrix `exp (t • G_Λ)` of the Λ-coalescent's block-counting process, with
`G_Λ = LambdaCoalescent.blockCountingGenerator Λ n` and Λ the measure whose moments are the
limits `lim q_k / c_N` of the offspring factorial moments.

Source: M. Möhle, S. Sagitov, *A classification of coalescent processes for haploid exchangeable
population models*, Ann. Probab. 29 (2001), Theorem 2.1 (Λ case: Sagitov 1999). Only the
block-counting process (number of ancestral lineages) and convergence of the finite-dimensional
transition matrices are covered; the partition-valued process and path-space (Skorokhod)
convergence are not. -/
theorem tendsto_lineageMatrix_pow (h : MohleSagitovLambda M Λ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun N => (M N).lineageMatrix n ^ ⌊t / (M N).coalProb⌋₊) atTop
      (𝓝 (NormedSpace.exp (t • LambdaCoalescent.blockCountingGenerator Λ n))) := by
  open scoped Matrix.Norms.Operator in
  refine (NormedSpace.tendsto_one_add_smul_pow h.tendsto_coalProb h.eventually_coalProb_pos
    (tendsto_smul_lineageMatrix_sub_one h n)
    (tendsto_floor_div_mul h.tendsto_coalProb h.eventually_coalProb_pos ht)).congr' ?_
  filter_upwards [h.eventually_coalProb_pos] with N hN
  rw [smul_smul, mul_inv_cancel₀ hN.ne', one_smul, add_sub_cancel]

omit [IsFiniteMeasure Λ] in
/-- Under the Möhle–Sagitov conditions Λ is a probability measure (`q_2 / c_N = 1`). -/
theorem measureReal_univ_eq_one (h : MohleSagitovLambda M Λ) : Λ.real Set.univ = 1 := by
  have h2 := h.tendsto_mergeProb_div 2 le_rfl
  simp only [Nat.sub_self, pow_zero, integral_const, smul_eq_mul, mul_one] at h2
  refine tendsto_nhds_unique h2 (tendsto_const_nhds.congr' ?_)
  filter_upwards [h.eventually_coalProb_pos] with N hN
  rw [coalProb] at hN ⊢
  rw [div_self hN.ne']

/-- **The limit Λ is determined by the offspring law**: two measures satisfying the
Möhle–Sagitov conditions for the same model coincide (their moments are the same limits;
Pitman's uniqueness theorem `LambdaCoalescent.eq_of_mergerRate_eq`). -/
theorem eq_of_mohleSagitovLambda {Λ' : Measure I} [IsFiniteMeasure Λ']
    (h : MohleSagitovLambda M Λ) (h' : MohleSagitovLambda M Λ') : Λ = Λ' := by
  refine LambdaCoalescent.eq_of_mergerRate_eq Λ Λ' fun k hk => ?_
  rw [LambdaCoalescent.mergerRate_of_le _ hk le_rfl, LambdaCoalescent.mergerRate_of_le _ hk le_rfl]
  simp only [Nat.sub_self, pow_zero, mul_one]
  exact tendsto_nhds_unique (h.tendsto_mergeProb_div k hk) (h'.tendsto_mergeProb_div k hk)

private lemma mergerRate_three_three :
    LambdaCoalescent.mergerRate Λ 3 3 = ∫ x, (x : ℝ) ^ (3 - 2) ∂Λ := by
  rw [LambdaCoalescent.mergerRate_of_le _ (by norm_num) le_rfl]
  simp

/-- The heavy-tail condition is the positivity of the limiting triple-merger rate
`λ_{3,3} = ∫ x Λ(dx)`. -/
theorem heavyTailed_iff_mergerRate_pos (h : MohleSagitovLambda M Λ) :
    HeavyTailed M ↔ 0 < LambdaCoalescent.mergerRate Λ 3 3 := by
  rw [mergerRate_three_three]
  constructor
  · rintro ⟨φ, hφ, hlim⟩
    rwa [tendsto_nhds_unique (h.tendsto_mergeProb_div 3 (by norm_num)) hlim]
  · intro hpos
    exact ⟨_, hpos, h.tendsto_mergeProb_div 3 (by norm_num)⟩

/-- **The tail condition separates Λ from Kingman.** Under the Möhle–Sagitov conditions, the
model is heavy-tailed iff the limit measure Λ is not Kingman's `δ₀`, i.e. iff Λ has mass away
from `0` and the limit coalescent has multiple mergers. -/
theorem heavyTailed_iff (h : MohleSagitovLambda M Λ) : HeavyTailed M ↔ Λ ≠ Measure.dirac 0 := by
  rw [heavyTailed_iff_mergerRate_pos h]
  constructor
  · rintro hpos rfl
    rw [LambdaCoalescent.mergerRate_dirac_zero] at hpos
    norm_num at hpos
  · intro hne
    by_contra hle
    have h0 : LambdaCoalescent.mergerRate Λ 3 3 = 0 :=
      le_antisymm (not_lt.1 hle) (LambdaCoalescent.mergerRate_nonneg Λ 3 3)
    refine hne (LambdaCoalescent.eq_of_mergerRate_eq Λ _ fun k hk => ?_)
    rw [LambdaCoalescent.mergerRate_dirac_zero]
    rcases eq_or_lt_of_le hk with rfl | hk3
    · rw [LambdaCoalescent.mergerRate_two_two, measureReal_univ_eq_one h]
      simp
    · rw [ite_eq_right (by omega)]
      refine le_antisymm ?_ (LambdaCoalescent.mergerRate_nonneg Λ k k)
      rw [← h0, mergerRate_three_three, LambdaCoalescent.mergerRate_of_le _ (by omega) le_rfl]
      simp only [Nat.sub_self, pow_zero, mul_one]
      refine integral_mono (integrable_pow _) (integrable_pow _) fun x => ?_
      exact pow_le_pow_of_le_one x.2.1 x.2.2 (by omega)

/-- Kingman's coalescent is the boundary case `Λ = δ₀` of the Λ-coalescent: its block-counting
generator is Kingman's pure-death generator (`k → k - 1` at rate `k choose 2`). -/
theorem blockCountingGenerator_dirac_zero (n : ℕ) :
    LambdaCoalescent.blockCountingGenerator (Measure.dirac 0) n =
      KingmanBlockCounting.blockCountingGenerator n := by
  ext i j
  simp only [LambdaCoalescent.blockCountingGenerator, KingmanBlockCounting.blockCountingGenerator,
    Matrix.of_apply, LambdaCoalescent.totalMergerRate_dirac_zero,
    LambdaCoalescent.mergerRate_dirac_zero, Fin.ext_iff]
  by_cases h1 : (i : ℕ) = j
  · simp [h1]
  by_cases h2 : (j : ℕ) < i
  · by_cases h3 : (j : ℕ) + 1 = i
    · have h4 : (i : ℕ) + 1 - j = 2 := by omega
      by_cases h5 : 2 ≤ (i : ℕ)
      · simp [h1, h2, h3, h4, h5]
      · have hi1 : (i : ℕ) = 1 := by omega
        simp [h3, hi1]
    · have h4 : (i : ℕ) + 1 - j ≠ 2 := by omega
      simp [h1, h2, h3, h4, show (j : ℕ) ≠ i by omega]
  · simp [h1, h2, show (j : ℕ) + 1 ≠ i by omega, show (j : ℕ) ≠ i by omega]

/-- **In the heavy-tailed case the limit is not Kingman's coalescent**: the limit generator has
a positive rate of triple mergers (three lineages to one), which Kingman's generator lacks. -/
theorem blockCountingGenerator_ne_kingman (h : MohleSagitovLambda M Λ) (hH : HeavyTailed M)
    {n : ℕ} (hn : 3 ≤ n) :
    LambdaCoalescent.blockCountingGenerator Λ n ≠
      KingmanBlockCounting.blockCountingGenerator n := by
  intro heq
  have h31 := congrFun (congrFun heq ⟨3, by omega⟩) ⟨1, by omega⟩
  simp only [LambdaCoalescent.blockCountingGenerator, KingmanBlockCounting.blockCountingGenerator,
    Matrix.of_apply, Fin.mk.injEq] at h31
  norm_num at h31
  exact (ne_of_gt ((heavyTailed_iff_mergerRate_pos h).1 hH)) h31

/-- **Heavy-tailed Cannings models converge to a Λ-coalescent with multiple mergers.** Under
the Möhle–Sagitov conditions and the heavy-tail condition, the limit measure Λ is not `δ₀`, the
limit has a positive triple-merger rate `λ_{3,3} = ∫ x Λ(dx)`, and the time-rescaled ancestral
lineage count converges to the Λ-coalescent's block-counting process. -/
theorem tendsto_lineageMatrix_pow_of_heavyTailed (h : MohleSagitovLambda M Λ)
    (hH : HeavyTailed M) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Λ ≠ Measure.dirac 0 ∧ 0 < LambdaCoalescent.mergerRate Λ 3 3 ∧
      Tendsto (fun N => (M N).lineageMatrix n ^ ⌊t / (M N).coalProb⌋₊) atTop
        (𝓝 (NormedSpace.exp (t • LambdaCoalescent.blockCountingGenerator Λ n))) :=
  ⟨(heavyTailed_iff h).1 hH, (heavyTailed_iff_mergerRate_pos h).1 hH,
    tendsto_lineageMatrix_pow h n ht⟩

/-- **The Kingman boundary.** When the Möhle–Sagitov conditions hold with `Λ = δ₀` (no heavy
tail), the Λ-coalescent limit is Kingman's: the time-rescaled lineage count converges to
Kingman's pure-death process with rates `k choose 2`. -/
theorem tendsto_lineageMatrix_pow_dirac_zero {M : (N : ℕ) → CanningsModel N}
    (h : MohleSagitovLambda M (Measure.dirac 0)) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun N => (M N).lineageMatrix n ^ ⌊t / (M N).coalProb⌋₊) atTop
      (𝓝 (NormedSpace.exp (t • KingmanBlockCounting.blockCountingGenerator n))) := by
  rw [← blockCountingGenerator_dirac_zero]
  exact tendsto_lineageMatrix_pow h n ht

end Limit

end MathlibExt.Biology.PopulationGenetics.Coalescent.CanningsLambda
