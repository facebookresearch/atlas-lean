/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalBayesNet
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Kernel causal Bayesian networks

A *kernel causal Bayesian network* on nodes `Fin n` in topological order
assigns to each node a set of earlier parents and a Markov kernel from its
parents' values, where each node ranges over a standard Borel space
(Forré, *Transitional Conditional Independence*, Defs. 5.15–5.16, without
input nodes). The joint law is the ordered product of the kernels.
Intervention `do(X_k = a)` deletes the parents of `k` and replaces its
kernel by the Dirac kernel at `a`.

Every finite `BayesNet` embeds into this framework: singletons under the
kernel joint are exactly the finite joint probabilities, and the embedding
commutes with intervention.

## Main definitions

* `KernelCBN`: parents and Markov kernels on standard Borel spaces.
* `KernelCBN.joint`: the joint law, a probability measure.
* `KernelCBN.intervene`: Dirac-kernel intervention with parents deleted.
* `BayesNet.toKernelCBN`: the embedding of finite Bayesian networks.

## Main results

* `BayesNet.toKernelCBN_joint_singleton`: the kernel joint of the embedding
  gives singleton `x` mass `ENNReal.ofReal (b.joint x)`.
* `KernelCBN.map_joint_intervene_apply_eq_dirac`: after `do(X_k = a)`, the
  law of `X_k` is `δ_a`.
* `BayesNet.toKernelCBN_intervene`: the embedding commutes with
  intervention.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

open MeasureTheory ProbabilityTheory

/-- A kernel causal Bayesian network on nodes `Fin n` in topological order
(Forré TCI Def 5.15, without input nodes): each node has parents among the
earlier nodes and a Markov kernel from its parents' values. -/
structure KernelCBN (n : ℕ) (Ω : Fin n → Type*) [∀ i, MeasurableSpace (Ω i)]
    [∀ i, StandardBorelSpace (Ω i)] where
  /-- The parents of node `k`, among `0, …, k - 1`. -/
  pa : (k : Fin n) → Finset (Fin k)
  /-- The conditional law of node `k` given its parents. -/
  kernel : (k : Fin n) → Kernel ((j : pa k) → Ω (Fin.castLE k.2.le j)) (Ω k)
  /-- Every conditional law is a Markov kernel. -/
  isMarkovKernel : ∀ k, IsMarkovKernel (kernel k)

namespace KernelCBN

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
  [∀ i, StandardBorelSpace (Ω i)] (c : KernelCBN n Ω)

instance (k : Fin n) : IsMarkovKernel (c.kernel k) := c.isMarkovKernel k

/-- The values of the parents of `⟨m, h⟩` read off a prefix assignment. -/
def parentValues (m : ℕ) (h : m < n) (x : (i : Fin m) → Ω (Fin.castLE h.le i)) :
    (j : c.pa ⟨m, h⟩) → Ω (Fin.castLE (⟨m, h⟩ : Fin n).2.le j) :=
  fun j => x ⟨j.1.1, j.1.2⟩

theorem measurable_parentValues (m : ℕ) (h : m < n) :
    Measurable (c.parentValues m h) := by
  exact Measurable.of_eval fun j => measurable_pi_apply _

/-- Joint law of the first `m` nodes (TCI Def 5.16, ordered product). -/
noncomputable def jointPrefix : (m : ℕ) → (h : m ≤ n) →
    Measure ((i : Fin m) → Ω (Fin.castLE h i))
  | 0, _ => Measure.dirac (fun i => i.elim0)
  | m + 1, h =>
      ((jointPrefix m (Nat.le_of_succ_le h)) ⊗ₘ
        ((c.kernel ⟨m, h⟩).comap (c.parentValues m h)
          (c.measurable_parentValues m h))).map (fun p => Fin.snoc p.1 p.2)

/-- The joint law of the network. -/
noncomputable def joint : Measure ((i : Fin n) → Ω i) :=
  c.jointPrefix n le_rfl

/-- The joint is a probability measure. -/
instance : IsProbabilityMeasure c.joint := by
  have h : ∀ (m : ℕ) (hm : m ≤ n), IsProbabilityMeasure (c.jointPrefix m hm) := by
    intro m
    induction m with
    | zero => intro hm; exact Measure.dirac.isProbabilityMeasure
    | succ m ih =>
      intro hm
      simp only [KernelCBN.jointPrefix]
      have hprob : IsProbabilityMeasure (c.jointPrefix m (Nat.le_of_succ_le hm)) := ih _
      have hker : IsMarkovKernel (c.kernel ⟨m, hm⟩) := c.isMarkovKernel _
      have hmarkov : IsMarkovKernel
          ((c.kernel ⟨m, hm⟩).comap (c.parentValues m hm)
            (c.measurable_parentValues m hm)) :=
        Kernel.IsMarkovKernel.comap (c.kernel ⟨m, hm⟩)
          (c.measurable_parentValues m hm)
      exact inferInstance
  exact h n le_rfl

/-- **Intervention** `do(X_k = a)`: delete the parents of `k` and replace
its kernel by the Dirac kernel at `a`; other nodes keep parents/kernels. -/
noncomputable def intervene (k : Fin n) (a : Ω k) : KernelCBN n Ω where
  pa j := if j = k then ∅ else c.pa j
  kernel j := if h : j = k then Kernel.const _ (Measure.dirac (h.symm ▸ a))
    else (c.kernel j).comap
      (fun z (i : c.pa j) => z ⟨i.1, by rw [ite_eq_right h]; exact i.2⟩) (by measurability)
  isMarkovKernel j := by
    split
    · infer_instance
    · infer_instance

/-- The intervened node has no parents. -/
theorem intervene_pa_self (k : Fin n) (a : Ω k) : (c.intervene k a).pa k = ∅ := by
  simp [intervene]

/-- Other nodes keep their parents under intervention. -/
theorem intervene_pa_of_ne {j k : Fin n} (hjk : j ≠ k) (a : Ω k) :
    (c.intervene k a).pa j = c.pa j := by
  simp [intervene, hjk]

/-- Every prefix joint is a probability measure. -/
theorem isProbabilityMeasure_jointPrefix : ∀ (m : ℕ) (hm : m ≤ n),
    IsProbabilityMeasure (c.jointPrefix m hm)
  | 0, _ => Measure.dirac.isProbabilityMeasure
  | m + 1, hm => by
    simp only [KernelCBN.jointPrefix]
    have hprob : IsProbabilityMeasure (c.jointPrefix m (Nat.le_of_succ_le hm)) :=
      isProbabilityMeasure_jointPrefix m _
    have hker : IsMarkovKernel (c.kernel ⟨m, hm⟩) := c.isMarkovKernel _
    have hmarkov : IsMarkovKernel ((c.kernel ⟨m, hm⟩).comap (c.parentValues m hm)
        (c.measurable_parentValues m hm)) :=
      Kernel.IsMarkovKernel.comap (c.kernel ⟨m, hm⟩) (c.measurable_parentValues m hm)
    exact inferInstance

/-- The `Fin.snoc` assembly map is measurable. -/
theorem measurable_snocMap {m : ℕ} (β : Fin (m + 1) → Type*) [∀ i, MeasurableSpace (β i)] :
    Measurable (fun p : ((i : Fin m) → β i.castSucc) × β (Fin.last m) =>
      Fin.snoc p.1 p.2) := by
  refine Measurable.of_eval fun i => ?_
  show Measurable fun p : ((i : Fin m) → β i.castSucc) × β (Fin.last m) =>
    Fin.snoc p.1 p.2 i
  by_cases hi : i = Fin.last m
  · subst hi
    simp only [Fin.snoc_last]
    exact measurable_snd
  · have hlt : i < Fin.last m := lt_of_le_of_ne (Fin.le_last i) hi
    have hi' : i.1 < m := hlt
    have hii : Fin.castSucc ⟨i.1, hi'⟩ = i := Fin.ext rfl
    rw [← hii]
    simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply _).comp measurable_fst

/-- The preimage of a singleton under `Fin.snoc` is a singleton. -/
theorem snoc_preimage_singleton {m : ℕ} (β : Fin (m + 1) → Type*)
    (y : (i : Fin (m + 1)) → β i) :
    (fun p : ((i : Fin m) → β i.castSucc) × β (Fin.last m) => Fin.snoc p.1 p.2) ⁻¹' {y} =
      {(Fin.init y, y (Fin.last m))} := by
  ext ⟨a, b⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  conv_lhs => rw [← Fin.snoc_init_self y]
  rw [Fin.snoc_inj]
  simp

/-- The kernel at the intervened node is the Dirac kernel. -/
theorem intervene_kernel_of_eq {k : Fin n} (j : Fin n) (hjk : j = k) (a : Ω k) :
    (c.intervene k a).kernel j = Kernel.const _ (Measure.dirac (hjk.symm ▸ a)) := by
  simp only [KernelCBN.intervene]
  rw [dite_eq_left hjk]
  rfl

/-- Prefix version: under intervention, the marginal at the intervened coordinate is Dirac. -/
theorem map_jointPrefix_intervene (k : Fin n) (a : Ω k) :
    ∀ (m : ℕ) (h : m ≤ n) (hkm : k.1 < m),
    ((c.intervene k a).jointPrefix m h).map (fun x => x ⟨k.1, hkm⟩) = Measure.dirac a
  | 0, h, hkm => by exact absurd hkm (Nat.not_lt_zero _)
  | m + 1, h, hkm => by
    have hprob : IsProbabilityMeasure
        ((c.intervene k a).jointPrefix m (Nat.le_of_succ_le h)) :=
      isProbabilityMeasure_jointPrefix _ m _
    have hker : IsMarkovKernel ((c.intervene k a).kernel ⟨m, h⟩) :=
      (c.intervene k a).isMarkovKernel _
    have hmarkov : IsMarkovKernel ((((c.intervene k a).kernel ⟨m, h⟩).comap
        ((c.intervene k a).parentValues m h)
        ((c.intervene k a).measurable_parentValues m h))) :=
      Kernel.IsMarkovKernel.comap _ _
    have hle : k.1 ≤ m := by omega
    rcases lt_or_eq_of_le hle with hlt | heq
    · have ih := map_jointPrefix_intervene k a m (Nat.le_of_succ_le h) hlt
      simp only [KernelCBN.jointPrefix]
      have hf : Measurable (fun p : ((i : Fin m) → Ω (Fin.castLE (Nat.le_of_succ_le h) i)) ×
          Ω ⟨m, h⟩ => Fin.snoc (α := fun i => Ω (Fin.castLE h i)) p.1 p.2) :=
        KernelCBN.measurable_snocMap (fun i => Ω (Fin.castLE h i))
      rw [Measure.map_map (measurable_pi_apply _) hf]
      have hfun : (fun x => x ⟨k.1, hkm⟩) ∘
            (fun p : ((i : Fin m) → Ω (Fin.castLE (Nat.le_of_succ_le h) i)) × Ω ⟨m, h⟩ =>
              Fin.snoc (α := fun i => Ω (Fin.castLE h i)) p.1 p.2) =
            (fun y : (i : Fin m) → Ω (Fin.castLE (Nat.le_of_succ_le h) i) => y ⟨k.1, hlt⟩) ∘
              Prod.fst := by
        funext p
        show Fin.snoc (α := fun i => Ω (Fin.castLE h i)) p.1 p.2 (Fin.castSucc ⟨k.1, hlt⟩) =
          p.1 ⟨k.1, hlt⟩
        rw [Fin.snoc_castSucc]
      rw [hfun, ← Measure.map_map (measurable_pi_apply _) measurable_fst, ← Measure.fst,
        Measure.fst_compProd]
      exact ih
    · subst heq
      simp only [KernelCBN.jointPrefix]
      have hf : Measurable (fun p : ((i : Fin k.1) → Ω (Fin.castLE (Nat.le_of_succ_le h) i)) ×
          Ω ⟨k.1, h⟩ => Fin.snoc (α := fun i => Ω (Fin.castLE h i)) p.1 p.2) :=
        KernelCBN.measurable_snocMap (fun i => Ω (Fin.castLE h i))
      rw [Measure.map_map (measurable_pi_apply _) hf]
      have hfun : (fun x => x ⟨k.1, hkm⟩) ∘
            (fun p : ((i : Fin k.1) → Ω (Fin.castLE (Nat.le_of_succ_le h) i)) × Ω ⟨k.1, h⟩ =>
              Fin.snoc (α := fun i => Ω (Fin.castLE h i)) p.1 p.2) =
            Prod.snd := by
        funext p
        show Fin.snoc (α := fun i => Ω (Fin.castLE h i)) p.1 p.2 (Fin.last k.1) = p.2
        rw [Fin.snoc_last]
      rw [hfun]
      have hjk : (⟨k.1, h⟩ : Fin n) = k := Fin.ext rfl
      rw [c.intervene_kernel_of_eq _ hjk _]
      rw [← Measure.snd, Measure.snd_compProd]
      show Measure.bind ((c.intervene k a).jointPrefix k.1 (Nat.le_of_succ_le h))
        (fun _ => Measure.dirac a) = Measure.dirac a
      rw [Measure.bind_const]
      have huniv := hprob.measure_univ
      rw [huniv, one_smul]

/-- After `do(X_k = a)`, the law of `X_k` is `δ_a`. -/
theorem map_joint_intervene_apply_eq_dirac (k : Fin n) (a : Ω k) :
    (c.intervene k a).joint.map (fun x => x k) = Measure.dirac a := by
  exact c.map_jointPrefix_intervene k a n le_rfl k.2

end KernelCBN

variable {α : Type*} {n : ℕ} [Fintype α] [Nonempty α] [MeasurableSpace α]
  [DiscreteMeasurableSpace α]

/-- A finite distribution (standard simplex point) as a measure. -/
noncomputable def stdSimplexMeasure (w : StdSimplex ℝ α) : Measure α :=
  ∑ a, ENNReal.ofReal (w.weights a) • Measure.dirac a

/-- The measure of a standard simplex point is a probability measure. -/
instance (w : StdSimplex ℝ α) : IsProbabilityMeasure (stdSimplexMeasure w) := by
  refine ⟨?_⟩
  rw [stdSimplexMeasure, Measure.finsetSum_apply]
  simp_rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => w.nonneg a), w.total_of_fintype,
    ENNReal.ofReal_one]

/-- A finite Bayesian network as a kernel causal Bayesian network. -/
noncomputable def BayesNet.toKernelCBN (b : BayesNet α n) :
    KernelCBN n (fun _ => α) where
  pa := b.pa
  kernel k := Kernel.ofFunOfCountable fun z => stdSimplexMeasure (b.cpt k z)
  isMarkovKernel k := by
    refine IsMarkovKernel.mk fun z => ?_
    show IsProbabilityMeasure (stdSimplexMeasure (b.cpt k z))
    infer_instance

/-- A finite distribution as a measure, evaluated on a singleton. -/
theorem stdSimplexMeasure_singleton (w : StdSimplex ℝ α) (b : α) :
    stdSimplexMeasure w {b} = ENNReal.ofReal (w.weights b) := by
  classical
  have hdirac : ∀ a : α, (Measure.dirac a : Measure α) {b} = if a = b then 1 else 0 := by
    classical
    intro a
    by_cases h : a = b
    · subst h
      rw [Measure.dirac_apply _ _, Set.indicator_of_mem (Set.mem_singleton_iff.mpr rfl) 1]
      simp
    · have hmem : a ∉ ({b} : Set α) := by rwa [Set.mem_singleton_iff]
      rw [Measure.dirac_apply _ _, Set.indicator_of_notMem hmem 1]
      simp [h]
  simp [stdSimplexMeasure, Measure.finsetSum_apply, Measure.smul_apply, hdirac, smul_eq_mul]

/-- Applying the embedded kernel. -/
theorem BayesNet.toKernelCBN_kernel_apply (b : BayesNet α n) (k : Fin n)
    (z : (j : (b.toKernelCBN).pa k) → α) :
    (b.toKernelCBN.kernel k) z = stdSimplexMeasure (b.cpt k z) := rfl

/-- The chain conditional of the network at a node is its table. -/
theorem BayesNet.toChain_cond_of_lt (b : BayesNet α n) {k : ℕ} (hk : k < n)
    (y : Fin k → α) :
    b.toChain.cond k y = b.cpt ⟨k, hk⟩ fun j => y j := by
  simp [BayesNet.toChain, hk]

/-- Prefix version of the discrete embedding. -/
theorem BayesNet.toKernelCBN_jointPrefix_singleton (b : BayesNet α n) :
    ∀ (m : ℕ) (h : m ≤ n) (y : Fin m → α),
    b.toKernelCBN.jointPrefix m h {y} = ENNReal.ofReal (b.toChain.joint m y)
  | 0, h, y => by
    simp only [KernelCBN.jointPrefix, Chain.joint_zero, ENNReal.ofReal_one]
    rw [Measure.dirac_apply_of_mem (Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))]
  | m + 1, h, y => by
    have hprob : IsProbabilityMeasure
        (b.toKernelCBN.jointPrefix m (Nat.le_of_succ_le h)) :=
      KernelCBN.isProbabilityMeasure_jointPrefix _ m _
    have hker : IsMarkovKernel ((b.toKernelCBN).kernel ⟨m, h⟩) :=
      (b.toKernelCBN).isMarkovKernel _
    have hmarkov : IsMarkovKernel (((b.toKernelCBN).kernel ⟨m, h⟩).comap
        ((b.toKernelCBN).parentValues m h) ((b.toKernelCBN).measurable_parentValues m h)) :=
      Kernel.IsMarkovKernel.comap _ _
    have ih := b.toKernelCBN_jointPrefix_singleton m
    simp only [KernelCBN.jointPrefix]
    rw [Measure.map_apply (KernelCBN.measurable_snocMap (fun _ => α))
      (measurableSet_singleton _)]
    rw [KernelCBN.snoc_preimage_singleton (fun _ => α) y, ← Set.singleton_prod_singleton]
    rw [Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _)]
    rw [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    have ih' := ih (Nat.le_of_succ_le h) (Fin.init y)
    rw [ih', Kernel.comap_apply, BayesNet.toKernelCBN_kernel_apply,
      stdSimplexMeasure_singleton]
    conv_rhs => rw [← Fin.snoc_init_self y, Chain.joint_snoc]
    rw [ENNReal.ofReal_mul (Chain.joint_nonneg _ _ _)]
    rw [b.toChain_cond_of_lt (Nat.lt_of_succ_le h) (Fin.init y)]
    rfl

/-- **Discrete embedding**: singletons under the kernel joint are the
finite joint probabilities. -/
theorem BayesNet.toKernelCBN_joint_singleton (b : BayesNet α n) (x : Fin n → α) :
    b.toKernelCBN.joint {x} = ENNReal.ofReal (b.joint x) := by
  exact b.toKernelCBN_jointPrefix_singleton n le_rfl x

/-- **Discrete embedding, density form**. -/
theorem BayesNet.toKernelCBN_joint_eq_withDensity (b : BayesNet α n) :
    b.toKernelCBN.joint =
      Measure.count.withDensity (fun x => ENNReal.ofReal (b.joint x)) := by
  apply Measure.ext_of_singleton
  intro x
  rw [b.toKernelCBN_joint_singleton, withDensity_apply _ (measurableSet_singleton _),
    Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
    Measure.count_singleton, one_mul]

/-- The measure of a point mass is the Dirac measure. -/
theorem stdSimplexMeasure_single (a : α) :
    stdSimplexMeasure (StdSimplex.single a) = Measure.dirac a := by
  classical
  apply Measure.ext_of_singleton
  intro b
  have hdirac : (Measure.dirac a : Measure α) {b} = if a = b then 1 else 0 := by
    by_cases h : a = b
    · subst h
      rw [Measure.dirac_apply _ _, Set.indicator_of_mem (Set.mem_singleton_iff.mpr rfl) 1]
      simp
    · have hmem : a ∉ ({b} : Set α) := by rwa [Set.mem_singleton_iff]
      rw [Measure.dirac_apply _ _, Set.indicator_of_notMem hmem 1]
      simp [h]
  rw [stdSimplexMeasure_singleton, StdSimplex.weights_single, Finsupp.single_apply, hdirac]
  by_cases h : a = b <;> simp [h]

/-- The embedding commutes with intervention. -/
theorem BayesNet.toKernelCBN_intervene (b : BayesNet α n) (k : Fin n) (a : α) :
    (b.intervene k a).toKernelCBN = b.toKernelCBN.intervene k a := by
  have hker : ((b.intervene k a).toKernelCBN).kernel
      = (b.toKernelCBN.intervene k a).kernel := by
    funext j
    by_cases hjk : j = k
    · subst hjk
      have hcpt : ∀ z, (b.intervene j a).cpt j z = StdSimplex.single a := by
        intro z
        simp [BayesNet.intervene]
      apply Kernel.ext
      intro z
      have eL : ((b.intervene j a).toKernelCBN).kernel j z
          = stdSimplexMeasure (StdSimplex.single a) := by
        show stdSimplexMeasure ((b.intervene j a).cpt j z)
          = stdSimplexMeasure (StdSimplex.single a)
        rw [hcpt z]
      have eR : ((b.toKernelCBN).intervene j a).kernel j z = Measure.dirac a := by
        have h := KernelCBN.intervene_kernel_of_eq (b.toKernelCBN) j rfl a
        exact (congrArg (fun F => F z) h).trans (Kernel.const_apply _ _)
      exact eL.trans ((stdSimplexMeasure_single a).trans eR.symm)
    · have hpa_eq : (b.intervene k a).pa j = b.pa j := by
        simp [BayesNet.intervene, hjk]
      have hpa_eq' : ((b.intervene k a).toKernelCBN).pa j = b.pa j := hpa_eq
      have hcpt : ∀ z, (b.intervene k a).cpt j z
          = b.cpt j (fun i => z ⟨i.1, by rw [hpa_eq]; exact i.2⟩) := by
        intro z
        simp [BayesNet.intervene, hjk]
      apply Kernel.ext
      intro z
      have eL : ((b.intervene k a).toKernelCBN).kernel j z
          = stdSimplexMeasure (b.cpt j
            (fun i => z ⟨i.1, by rw [hpa_eq']; exact i.2⟩)) := by
        show stdSimplexMeasure ((b.intervene k a).cpt j z)
          = stdSimplexMeasure (b.cpt j (fun i => z ⟨i.1, by rw [hpa_eq']; exact i.2⟩))
        rw [show (b.intervene k a).cpt j z
          = b.cpt j (fun i => z ⟨i.1, by rw [hpa_eq']; exact i.2⟩) from hcpt z]
      have eR : ((b.toKernelCBN).intervene k a).kernel j z
          = stdSimplexMeasure (b.cpt j
            (fun i => z ⟨i.1, by rw [hpa_eq']; exact i.2⟩)) := by
        simp only [KernelCBN.intervene]
        rw [dite_eq_right hjk]
        exact (Kernel.comap_apply _ _ _).trans (BayesNet.toKernelCBN_kernel_apply _ _ _)
      have mid : stdSimplexMeasure (b.cpt j
            (fun i => z ⟨i.1, by rw [hpa_eq']; exact i.2⟩))
          = stdSimplexMeasure (b.cpt j
            (fun i => z ⟨i.1, by rw [hpa_eq']; exact i.2⟩)) := rfl
      exact eL.trans (mid.trans eR.symm)
  have e1 : (b.intervene k a).toKernelCBN
      = { pa := ((b.intervene k a).toKernelCBN).pa,
          kernel := ((b.intervene k a).toKernelCBN).kernel,
          isMarkovKernel := ((b.intervene k a).toKernelCBN).isMarkovKernel } := rfl
  have e2 : b.toKernelCBN.intervene k a
      = { pa := (b.toKernelCBN.intervene k a).pa,
          kernel := (b.toKernelCBN.intervene k a).kernel,
          isMarkovKernel := (b.toKernelCBN.intervene k a).isMarkovKernel } := rfl
  rw [e1, e2, KernelCBN.mk.injEq]
  exact ⟨rfl, heq_of_eq hker⟩

end Cslib.MachineLearning.GraphicalModels
