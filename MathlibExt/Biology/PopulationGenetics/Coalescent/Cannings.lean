/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import MathlibExt.Probability.ProbabilityMassFunction.Expectation
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fintype

/-!
# Cannings models

A **Cannings model** (Cannings 1974) of a haploid population of constant size `N` produces each
generation from the previous one by an exchangeable offspring vector `(ν_1, …, ν_N)`,
`∑ ν_i = N`, independently across generations. We encode one generation as the law of its
parent map `f : Fin N → Fin N`, a `PMF` (`CanningsModel`), exchangeable in children and in
parents; the offspring numbers are `ν_i = #{c | f c = i}` (`CanningsModel.offspring`).

This file holds the model and its sampling API, shared by the Λ-coalescent limit
(`CanningsLambda`) and the Kingman limit (`CanningsKingman`). `sampleProb E` is the probability
of an event `E` for the parents of `m` sampled lineages; by exchangeability in the children it is
the same for any `m` distinct children (`sum_law_comp_emb`, `sampleProb_comp_emb`). From it come
the probability `mergeProb k` that `k` lineages share a parent, the coalescence probability
`coalProb = mergeProb 2`, the probability `doubleMergeProb` of a simultaneous double merger, and
the one-generation transition matrix `lineageMatrix n` of the ancestral lineage count.
Real-valued probabilities use the masses `(law f).toReal`, which sum to `1` (`sum_toReal_law`).
`expect F` is the expectation of a real function `F` of the whole parent map, which is
`PMF.expect` under `law` (`expect_eq_law_expect`); `sampleLaw hb` is the law of the parents of
the first `b` children, and expectations of functions of a sample are `PMF.expect` under it
(`expect_sampleLaw`). Both are invariant under relabeling children (`expect_comp_perm`,
`expect_sampleLaw_comp_perm`) and parents (`expect_perm_comp`, `expect_sampleLaw_perm_comp`,
`expect_offspring_comp_perm`), and are shared by both limits.

## References

* C. Cannings, *The latent roots of certain Markov chains arising in genetics: a new approach,
  I. Haploid models*, Adv. Appl. Probab. 6 (1974), 260–290.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings

open Finset

/-- A **Cannings model** of a haploid population of constant size `N`, as the law of one
generation's parent map: child `c` of the new generation has parent `f c` in the previous one.
The law is exchangeable in the children (relabelling the children `f ↦ f ∘ τ`) and in the
parents (relabelling the parents `f ↦ σ ∘ f`). The offspring vector `ν_i = #{c | f c = i}`
(`offspring`) is then an exchangeable vector summing to `N`, and given `ν` the children are
assigned to parents uniformly at random; this is Cannings' model (Cannings 1974). Successive
generations are independent copies of this law. Real-valued probabilities use the masses
`(law f).toReal`. -/
structure CanningsModel (N : ℕ) where
  /-- The law of one generation's parent map: `law f` is the probability of the parent map `f`. -/
  law : PMF (Fin N → Fin N)
  /-- Exchangeability in the children. -/
  law_comp_perm : ∀ (τ : Equiv.Perm (Fin N)) (f : Fin N → Fin N), law (f ∘ τ) = law f
  /-- Exchangeability in the parents. -/
  law_perm_comp : ∀ (σ : Equiv.Perm (Fin N)) (f : Fin N → Fin N), law (σ ∘ f) = law f

namespace CanningsModel

variable {N : ℕ} (M : CanningsModel N)

/-- The number of offspring `ν_i = #{c | f c = i}` of parent `i` under the parent map `f`. -/
def offspring (f : Fin N → Fin N) (i : Fin N) : ℕ := #{c | f c = i}

/-- The real masses `(law f).toReal` of the law sum to `1`. -/
theorem sum_toReal_law : ∑ f, (M.law f).toReal = 1 := by
  have h : ∑ f, M.law f = 1 := by
    rw [← tsum_fintype (L := SummationFilter.unconditional _)]
    exact M.law.tsum_coe
  rw [← ENNReal.toReal_sum fun f _ => M.law.apply_ne_top f, h, ENNReal.toReal_one]

/-- The probability that the parents `g = f ∘ castLE` of the first `m` children satisfy the event
`E`. By exchangeability in the children this is the probability of `E` for the parents of any
`m` distinct children (`sum_law_comp_emb`), i.e. for a sample of `m` lineages traced back one
generation. It is defined to be `0` when `m > N`. -/
def sampleProb {m : ℕ} (E : (Fin m → Fin N) → Prop) [DecidablePred E] : ℝ :=
  if h : m ≤ N then ∑ f, (M.law f).toReal * if E (f ∘ Fin.castLE h) then 1 else 0 else 0

/-- The probability that `k` sampled lineages all have the same parent one generation back
(a `k`-merger among `k` lineages); `mergeProb_mul_descFactorial` expresses it through the
offspring factorial moment `E[(ν_1)_k]`. -/
def mergeProb (k : ℕ) : ℝ := M.sampleProb fun g : Fin k → Fin N => ∀ i j, g i = g j

/-- The **coalescence probability** `c_N`: two sampled lineages have the same parent,
`c_N = E[ν_1 (ν_1 - 1)] / (N - 1)`. It sets the coalescent time scale. -/
def coalProb : ℝ := M.mergeProb 2

/-- The probability of a **simultaneous double merger**: among four sampled lineages, the first
two share a parent, the last two share a parent, and the two parents differ. -/
def doubleMergeProb : ℝ :=
  M.sampleProb fun g : Fin 4 → Fin N => g 0 = g 1 ∧ g 2 = g 3 ∧ g 0 ≠ g 2

/-- The one-generation transition probability of the **ancestral lineage count**: `b` sampled
lineages have exactly `a` distinct parents. -/
def lineageProb (b a : ℕ) : ℝ := M.sampleProb fun g : Fin b → Fin N => #(univ.image g) = a

/-- The one-generation transition matrix of the ancestral lineage count (block-counting
process) of a sample of at most `n` lineages, on the states `0, …, n`. -/
def lineageMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun b a => M.lineageProb b a

theorem sampleProb_congr {m : ℕ} {E E' : (Fin m → Fin N) → Prop} [DecidablePred E]
    [DecidablePred E'] (h : ∀ g, E g ↔ E' g) : M.sampleProb E = M.sampleProb E' := by
  unfold sampleProb
  split_ifs
  · exact sum_congr rfl fun f _ => by rw [if_congr (h _) rfl rfl]
  · rfl

theorem sampleProb_of_le {m : ℕ} (E : (Fin m → Fin N) → Prop) [DecidablePred E] (h : m ≤ N) :
    M.sampleProb E = ∑ f, (M.law f).toReal * if E (f ∘ Fin.castLE h) then 1 else 0 := by
  simp [sampleProb, h]

/-- Every embedding `Fin m ↪ Fin N` extends `Fin.castLE` along a permutation of `Fin N`. -/
private lemma exists_perm_comp_castLE {m : ℕ} (e : Fin m ↪ Fin N) (h : m ≤ N) :
    ∃ τ : Equiv.Perm (Fin N), ∀ i : Fin m, τ (Fin.castLE h i) = e i := by
  classical
  set F : Fin N → Fin N := fun c => if hc : (c : ℕ) < m then e ⟨c, hc⟩ else c with hF
  have hinj : Set.InjOn F ↑(univ.filter fun c : Fin N => (c : ℕ) < m) := by
    intro x hx y hy hxy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
    simp only [hF, hx, hy, dite_true] at hxy
    exact Fin.ext (by simpa using congrArg Fin.val (e.injective hxy))
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq (t := (univ : Finset (Fin N)))
    (by simp) (subset_univ _) hinj
  refine ⟨g.trans (Equiv.subtypeUnivEquiv mem_univ), fun i => ?_⟩
  have := hg (Fin.castLE h i) (by simp)
  simp only [Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply] at this ⊢
  rw [this, hF]
  simp

/-- **Exchangeability of samples.** The event `E` for the parents of the children
`e 0, …, e (m - 1)` (any `m` distinct children) has probability `sampleProb E`. -/
theorem sum_law_comp_emb {m : ℕ} (e : Fin m ↪ Fin N) (E : (Fin m → Fin N) → Prop)
    [DecidablePred E] :
    ∑ f, (M.law f).toReal * (if E (f ∘ e) then 1 else 0) = M.sampleProb E := by
  have hmN : m ≤ N := by simpa using Fintype.card_le_of_embedding e
  obtain ⟨τ, hτ⟩ := exists_perm_comp_castLE e hmN
  rw [sampleProb_of_le _ _ hmN]
  have he : ∀ f : Fin N → Fin N, f ∘ e = (f ∘ τ) ∘ Fin.castLE hmN := fun f => by
    funext i; simp [hτ]
  simp_rw [he]
  refine Fintype.sum_equiv (Equiv.arrowCongr τ.symm (Equiv.refl _)) _ _ fun f => ?_
  change _ = (M.law (f ∘ τ)).toReal * _
  rw [M.law_comp_perm τ f]
  rfl

/-- Events for a subsample: the event `E` for the parents of the lineages `u 0, …, u (m - 1)`
of a sample of `b` has probability `sampleProb E`. -/
theorem sampleProb_comp_emb {b m : ℕ} (hb : b ≤ N) (u : Fin m ↪ Fin b)
    (E : (Fin m → Fin N) → Prop) [DecidablePred E] :
    M.sampleProb (fun g : Fin b → Fin N => E (g ∘ u)) = M.sampleProb E := by
  rw [sampleProb_of_le _ _ hb, ← M.sum_law_comp_emb (u.trans (Fin.castLEEmb hb))]
  rfl

theorem sampleProb_nonneg {m : ℕ} (E : (Fin m → Fin N) → Prop) [DecidablePred E] :
    0 ≤ M.sampleProb E := by
  unfold sampleProb
  split_ifs
  · exact sum_nonneg fun f _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)
  · exact le_rfl

theorem offspring_comp_perm (f : Fin N → Fin N) (τ : Equiv.Perm (Fin N)) (i : Fin N) :
    offspring (f ∘ τ) i = offspring f i := by
  unfold offspring
  exact card_equiv τ (by simp)

theorem offspring_perm_comp (f : Fin N → Fin N) (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    offspring (σ ∘ f) i = offspring f (σ.symm i) := by
  unfold offspring
  congr 1
  exact filter_congr fun c _ => (Equiv.eq_symm_apply σ).symm

/-! ### Expectations -/

/-- Expectation of a real function of the whole parent map, with the masses `(law f).toReal`. -/
def expect (F : (Fin N → Fin N) → ℝ) : ℝ := ∑ f, (M.law f).toReal * F f

/-- The expectation is `PMF.expect` under the law of the parent map. -/
theorem expect_eq_law_expect (F : (Fin N → Fin N) → ℝ) : M.expect F = M.law.expect F :=
  (PMF.expect_eq_sum M.law F).symm

theorem expect_add (F G : (Fin N → Fin N) → ℝ) :
    M.expect (fun f => F f + G f) = M.expect F + M.expect G := by
  simp only [expect_eq_law_expect]
  exact PMF.expect_add (f := F) (g := G)

theorem expect_sub (F G : (Fin N → Fin N) → ℝ) :
    M.expect (fun f => F f - G f) = M.expect F - M.expect G := by
  rw [eq_sub_iff_add_eq, ← M.expect_add]
  simp only [sub_add_cancel]

theorem expect_const_mul (a : ℝ) (F : (Fin N → Fin N) → ℝ) :
    M.expect (fun f => a * F f) = a * M.expect F := by
  simp only [expect_eq_law_expect]
  exact PMF.expect_const_mul a F

theorem expect_const (a : ℝ) : M.expect (fun _ => a) = a := by
  rw [expect_eq_law_expect]
  exact PMF.expect_const M.law a

theorem expect_sum {ι : Type*} (s : Finset ι) (F : ι → (Fin N → Fin N) → ℝ) :
    M.expect (fun f => ∑ i ∈ s, F i f) = ∑ i ∈ s, M.expect (F i) := by
  simp only [expect_eq_law_expect]
  exact PMF.expect_sum s F

theorem expect_mono {F G : (Fin N → Fin N) → ℝ} (h : ∀ f, F f ≤ G f) :
    M.expect F ≤ M.expect G := by
  simp only [expect_eq_law_expect]
  exact PMF.expect_le_expect h

theorem expect_nonneg {F : (Fin N → Fin N) → ℝ} (h : ∀ f, 0 ≤ F f) : 0 ≤ M.expect F := by
  rw [expect_eq_law_expect]
  exact PMF.expect_nonneg h

/-- Relabeling the children does not change expectations. -/
theorem expect_comp_perm (σ : Equiv.Perm (Fin N)) (F : (Fin N → Fin N) → ℝ) :
    M.expect (fun f => F (f ∘ σ)) = M.expect F := by
  let e : (Fin N → Fin N) ≃ (Fin N → Fin N) :=
    { toFun := fun f => f ∘ σ
      invFun := fun f => f ∘ σ.symm
      left_inv := fun f => by funext; simp
      right_inv := fun f => by funext; simp }
  exact Fintype.sum_equiv e _ _ fun f => by simp [e, M.law_comp_perm]

/-- Relabeling the parents does not change expectations. -/
theorem expect_perm_comp (σ : Equiv.Perm (Fin N)) (F : (Fin N → Fin N) → ℝ) :
    M.expect (fun f => F (σ ∘ f)) = M.expect F := by
  let e : (Fin N → Fin N) ≃ (Fin N → Fin N) :=
    { toFun := fun f => σ ∘ f
      invFun := fun f => σ.symm ∘ f
      left_inv := fun f => by funext; simp
      right_inv := fun f => by funext; simp }
  exact Fintype.sum_equiv e _ _ fun f => by simp [e, M.law_perm_comp]

/-- **Exchangeable offspring numbers**: the offspring vector `(ν_1, …, ν_N)` has the same law
as `(ν_{σ 1}, …, ν_{σ N})` for every permutation `σ`. -/
theorem expect_offspring_comp_perm (σ : Equiv.Perm (Fin N)) (F : (Fin N → ℕ) → ℝ) :
    M.expect (fun f => F (offspring f ∘ σ)) = M.expect fun f => F (offspring f) := by
  have h : ∀ f : Fin N → Fin N, offspring f ∘ σ = offspring (σ.symm ∘ f) := fun f => by
    funext j
    rw [Function.comp_apply, offspring_perm_comp, Equiv.symm_symm]
  simp_rw [h]
  exact M.expect_perm_comp σ.symm (fun f => F (offspring f))

/-- The law of the parents `f ∘ Fin.castLE hb` of the first `b` children. Expectations of real
functions of a sample are `PMF.expect` under it, with its linearity and monotonicity lemmas. -/
noncomputable def sampleLaw {b : ℕ} (hb : b ≤ N) : PMF (Fin b → Fin N) :=
  M.law.map fun f => f ∘ Fin.castLE hb

section SampleLaw

variable {b : ℕ} {hb : b ≤ N}

/-- A sampled expectation is the expectation of the observable on the first `b` children. -/
theorem expect_sampleLaw (F : (Fin b → Fin N) → ℝ) :
    (M.sampleLaw hb).expect F = M.expect fun f => F (f ∘ Fin.castLE hb) := by
  rw [sampleLaw, PMF.expect_map, expect_eq_law_expect]
  rfl

/-- Relabeling the parents does not change sampled expectations. -/
theorem expect_sampleLaw_perm_comp (σ : Equiv.Perm (Fin N)) (F : (Fin b → Fin N) → ℝ) :
    (M.sampleLaw hb).expect (fun g => F (σ ∘ g)) = (M.sampleLaw hb).expect F := by
  rw [expect_sampleLaw, expect_sampleLaw]
  exact M.expect_perm_comp σ fun f => F (f ∘ Fin.castLE hb)

/-- Relabeling the sampled children does not change sampled expectations: the relabeling of the
`b` sampled children extends to a permutation of all `N` children. -/
theorem expect_sampleLaw_comp_perm (σ : Equiv.Perm (Fin b)) (F : (Fin b → Fin N) → ℝ) :
    (M.sampleLaw hb).expect (fun g => F (g ∘ σ)) = (M.sampleLaw hb).expect F := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hb ∘ σ) (Fin.castLE hb)
    ((Fin.castLE_injective hb).comp σ.injective) (Fin.castLE_injective hb)
  have h : ∀ f : Fin N → Fin N, (f ∘ Fin.castLE hb) ∘ σ = (f ∘ τ.symm) ∘ Fin.castLE hb := by
    intro f
    funext i
    simp only [Function.comp_apply, ← hτ i, Equiv.symm_apply_apply]
  rw [expect_sampleLaw, expect_sampleLaw]
  simp_rw [h]
  exact M.expect_comp_perm τ.symm fun f => F (f ∘ Fin.castLE hb)

end SampleLaw

end CanningsModel

end MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings
