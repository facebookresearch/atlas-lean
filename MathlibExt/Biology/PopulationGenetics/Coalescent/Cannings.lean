/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic
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
`sampleExpect hb F` is the expectation of a real function `F` of the parents of the first `b`
children, and `expect F` that of a function of the whole parent map, the case `b = N`
(`expect_eq_sampleExpect`). Their linearity and monotonicity lemmas, and their invariance under
relabeling children (`sampleExpect_comp_perm`, `expect_comp_perm`) and parents
(`sampleExpect_perm_comp`, `expect_perm_comp`, `expect_offspring_comp_perm`), are shared by both
limits.

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

/-- Expectation `E[F (f ∘ Fin.castLE hb)]` of a real function `F` of the parents of the first `b`
children, with the masses `(law f).toReal`. -/
def sampleExpect {b : ℕ} (hb : b ≤ N) (F : (Fin b → Fin N) → ℝ) : ℝ :=
  ∑ f, (M.law f).toReal * F (f ∘ Fin.castLE hb)

/-- Expectation of a real function of the whole parent map, with the masses `(law f).toReal`. -/
def expect (F : (Fin N → Fin N) → ℝ) : ℝ := ∑ f, (M.law f).toReal * F f

/-- The whole-map expectation is the sampled expectation of all `N` children: `f ∘ Fin.castLE
le_rfl` is `f` by definition. -/
theorem expect_eq_sampleExpect (F : (Fin N → Fin N) → ℝ) :
    M.expect F = M.sampleExpect le_rfl F :=
  rfl

section SampleExpect

variable {b : ℕ} {hb : b ≤ N}

theorem sampleExpect_add (F G : (Fin b → Fin N) → ℝ) :
    M.sampleExpect hb (fun g => F g + G g) = M.sampleExpect hb F + M.sampleExpect hb G := by
  simp only [sampleExpect, mul_add, sum_add_distrib]

theorem sampleExpect_sub (F G : (Fin b → Fin N) → ℝ) :
    M.sampleExpect hb (fun g => F g - G g) = M.sampleExpect hb F - M.sampleExpect hb G := by
  simp only [sampleExpect, mul_sub, sum_sub_distrib]

theorem sampleExpect_const_mul (a : ℝ) (F : (Fin b → Fin N) → ℝ) :
    M.sampleExpect hb (fun g => a * F g) = a * M.sampleExpect hb F := by
  simp only [sampleExpect, mul_sum]
  exact sum_congr rfl fun f _ => by ring

theorem sampleExpect_const (a : ℝ) : M.sampleExpect hb (fun _ => a) = a := by
  simp only [sampleExpect, ← sum_mul, M.sum_toReal_law, one_mul]

theorem sampleExpect_sum {ι : Type*} (s : Finset ι) (F : ι → (Fin b → Fin N) → ℝ) :
    M.sampleExpect hb (fun g => ∑ i ∈ s, F i g) = ∑ i ∈ s, M.sampleExpect hb (F i) := by
  simp only [sampleExpect, mul_sum]
  exact sum_comm

theorem sampleExpect_mono {F G : (Fin b → Fin N) → ℝ} (h : ∀ g, F g ≤ G g) :
    M.sampleExpect hb F ≤ M.sampleExpect hb G :=
  sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (h _) ENNReal.toReal_nonneg

theorem sampleExpect_nonneg {F : (Fin b → Fin N) → ℝ} (h : ∀ g, 0 ≤ F g) :
    0 ≤ M.sampleExpect hb F :=
  sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (h _)

/-- Relabeling the parents does not change sampled expectations. -/
theorem sampleExpect_perm_comp (σ : Equiv.Perm (Fin N)) (F : (Fin b → Fin N) → ℝ) :
    M.sampleExpect hb (fun g => F (σ ∘ g)) = M.sampleExpect hb F := by
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) σ) _ _ fun f => ?_
  change _ = (M.law (σ ∘ f)).toReal * F ((σ ∘ f) ∘ Fin.castLE hb)
  rw [M.law_perm_comp σ f]
  rfl

/-- Relabeling the sampled children does not change sampled expectations. -/
theorem sampleExpect_comp_perm (σ : Equiv.Perm (Fin b)) (F : (Fin b → Fin N) → ℝ) :
    M.sampleExpect hb (fun g => F (g ∘ σ)) = M.sampleExpect hb F := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hb ∘ σ) (Fin.castLE hb)
    ((Fin.castLE_injective hb).comp σ.injective) (Fin.castLE_injective hb)
  refine Fintype.sum_equiv (Equiv.arrowCongr τ (Equiv.refl _)) _ _ fun f => ?_
  have h : (f ∘ Fin.castLE hb) ∘ σ = (f ∘ τ.symm) ∘ Fin.castLE hb := by
    funext i
    simp only [Function.comp_apply, ← hτ i, Equiv.symm_apply_apply]
  change _ = (M.law (f ∘ τ.symm)).toReal * F ((f ∘ τ.symm) ∘ Fin.castLE hb)
  rw [M.law_comp_perm τ.symm f, ← h]

end SampleExpect

/-! The whole-map expectation inherits the sampled lemmas at `b = N`. -/

theorem expect_add (F G : (Fin N → Fin N) → ℝ) :
    M.expect (fun f => F f + G f) = M.expect F + M.expect G :=
  M.sampleExpect_add (hb := le_rfl) F G

theorem expect_sub (F G : (Fin N → Fin N) → ℝ) :
    M.expect (fun f => F f - G f) = M.expect F - M.expect G :=
  M.sampleExpect_sub (hb := le_rfl) F G

theorem expect_const_mul (a : ℝ) (F : (Fin N → Fin N) → ℝ) :
    M.expect (fun f => a * F f) = a * M.expect F :=
  M.sampleExpect_const_mul (hb := le_rfl) a F

theorem expect_const (a : ℝ) : M.expect (fun _ => a) = a :=
  M.sampleExpect_const (hb := le_rfl) a

theorem expect_sum {ι : Type*} (s : Finset ι) (F : ι → (Fin N → Fin N) → ℝ) :
    M.expect (fun f => ∑ i ∈ s, F i f) = ∑ i ∈ s, M.expect (F i) :=
  M.sampleExpect_sum (hb := le_rfl) s F

theorem expect_mono {F G : (Fin N → Fin N) → ℝ} (h : ∀ f, F f ≤ G f) :
    M.expect F ≤ M.expect G :=
  M.sampleExpect_mono (hb := le_rfl) h

theorem expect_nonneg {F : (Fin N → Fin N) → ℝ} (h : ∀ f, 0 ≤ F f) : 0 ≤ M.expect F :=
  M.sampleExpect_nonneg (hb := le_rfl) h

/-- Relabeling the children does not change expectations. -/
theorem expect_comp_perm (σ : Equiv.Perm (Fin N)) (F : (Fin N → Fin N) → ℝ) :
    M.expect (fun f => F (f ∘ σ)) = M.expect F :=
  M.sampleExpect_comp_perm (hb := le_rfl) σ F

/-- Relabeling the parents does not change expectations. -/
theorem expect_perm_comp (σ : Equiv.Perm (Fin N)) (F : (Fin N → Fin N) → ℝ) :
    M.expect (fun f => F (σ ∘ f)) = M.expect F :=
  M.sampleExpect_perm_comp (hb := le_rfl) σ F

/-- **Exchangeable offspring numbers**: the offspring vector `(ν_1, …, ν_N)` has the same law
as `(ν_{σ 1}, …, ν_{σ N})` for every permutation `σ`. -/
theorem expect_offspring_comp_perm (σ : Equiv.Perm (Fin N)) (F : (Fin N → ℕ) → ℝ) :
    M.expect (fun f => F (offspring f ∘ σ)) = M.expect fun f => F (offspring f) := by
  have h : ∀ f : Fin N → Fin N, offspring f ∘ σ = offspring (σ.symm ∘ f) := fun f => by
    funext j
    rw [Function.comp_apply, offspring_perm_comp, Equiv.symm_symm]
  simp_rw [h]
  exact M.expect_perm_comp σ.symm (fun f => F (offspring f))

end CanningsModel

end MathlibExt.Biology.PopulationGenetics.Coalescent.Cannings
