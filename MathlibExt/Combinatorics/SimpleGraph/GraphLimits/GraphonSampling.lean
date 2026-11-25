/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.Graphon
public import MathlibExt.Combinatorics.FinitelyForcibleGraphons
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Every graphon is a graph limit

For every graphon `W` (in the sense of `IsGraphon`: jointly measurable, symmetric, with values in
`[0, 1]`) there is a sequence of nonempty simple graphs `Gₙ` with `t(F, Gₙ) → t(F, W)` for every
simple graph `F` (`exists_graph_sequence_tendsto`).

The graphs are `W`-random graphs `G(n, W)` (L. Lovász and B. Szegedy, *Limits of dense graph
sequences*, J. Combin. Theory Ser. B 96 (2006), 933-957; arXiv:math/0408173v2, §2.6): the
vertices `1, …, n` get independent uniform types `xᵢ ∈ [0, 1]`, and `ij` is an edge when an
independent uniform variable `Uᵢⱼ ∈ [0, 1]` falls below `W(xᵢ, xⱼ)`, that is, with probability
`W(xᵢ, xⱼ)`. The proof is the second moment method, as in Lemma 2.4 of the arXiv version and the
Chebyshev bound after it.

* Read through an injective map `Fin k → Fin n`, the sample is again an independent uniform
  sample, so the expected weight of an injective map is `t(F, W)`, and two injective maps with
  disjoint images have uncorrelated weights.
* At most a `(2k)² / n` fraction of the pairs of maps `Fin k → Fin n` are not injective with
  disjoint images, so the mean square deviation of `t(F, G(n, W))` from `t(F, W)` is at most
  `(2k)² / n`.
* For each `m` and `n` large, the first moment method gives one sample whose graph is within
  `1 / (m + 1)` of `W` in the densities of all the finitely many graphs on at most `m` vertices;
  these graphs form the sequence.

This uses only the convergence of `t(F, G(n, W))` to `t(F, W)` in mean square, not its almost
sure convergence, which suffices for the existence of the sequence.
-/

public section

namespace MathlibExt.Combinatorics.SimpleGraph.GraphLimitsWanted

open MeasureTheory Set Filter Topology
open MathlibExt.Combinatorics.SimpleGraph.GraphLimits
open MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted (IsGraphon)

/-- The uniform probability measure on `[0, 1]`. -/
private noncomputable abbrev sampleMeasure : Measure ℝ := volume.restrict (Icc 0 1)

private instance sampleMeasure.isProbabilityMeasure : IsProbabilityMeasure sampleMeasure :=
  ⟨by simp [sampleMeasure, Real.volume_Icc]⟩

/-- Reading an independent uniform sample through an injective map of the coordinates gives an
independent uniform sample. -/
private lemma measurePreserving_comp {ι κ : Type*} [Fintype ι] [Fintype κ] {j : κ → ι}
    (hj : Function.Injective j) :
    MeasurePreserving (fun ω : ι → ℝ => ω ∘ j) (Measure.pi fun _ : ι => sampleMeasure)
      (Measure.pi fun _ : κ => sampleMeasure) := by
  classical
  have hm : Measurable fun ω : ι → ℝ => ω ∘ j :=
    Measurable.of_eval fun c => measurable_pi_apply (j c)
  refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  set t : ι → Set ℝ := Function.extend j s fun _ => univ with ht
  have pre : (fun ω : ι → ℝ => ω ∘ j) ⁻¹' univ.pi s = univ.pi t := by
    ext ω
    simp only [mem_preimage, mem_univ_pi, Function.comp_apply]
    constructor
    · intro h i
      by_cases hi : ∃ c, j c = i
      · obtain ⟨c, rfl⟩ := hi
        rw [ht, hj.extend_apply]
        exact h c
      · rw [ht, Function.extend_apply' _ _ _ hi]
        exact mem_univ _
    · intro h c
      have := h (j c)
      rwa [ht, hj.extend_apply] at this
  rw [pre, Measure.pi_pi]
  symm
  refine Fintype.prod_of_injective j hj _ _ (fun i hi => ?_) (fun c => ?_)
  · rw [ht, Function.extend_apply' _ _ _ (by simpa using hi)]
    simp
  · rw [ht, hj.extend_apply]

/-- The `W`-random graph on `V` driven by `ω`: the vertex `i` has type `ω (inl i)`, and `ij` is
an edge when the uniform variable `ω (inr s(i, j))` falls below `W` at the types of `i` and `j`. -/
private def sampleGraph {V : Type*} (W : ℝ → ℝ → ℝ) (ω : V ⊕ Sym2 V → ℝ) : SimpleGraph V :=
  SimpleGraph.fromRel fun i j => ω (.inr s(i, j)) < W (ω (.inl i)) (ω (.inl j))

private noncomputable instance sampleGraph.decidableRel {V : Type*} (W : ℝ → ℝ → ℝ)
    (ω : V ⊕ Sym2 V → ℝ) : DecidableRel (sampleGraph W ω).Adj :=
  Classical.decRel _

/-- The coordinates that an injective map `φ` of vertices reads. -/
private def sampleMap {α V : Type*} (φ : α → V) : α ⊕ Sym2 α → V ⊕ Sym2 V :=
  Sum.map φ (Sym2.map φ)

private lemma sampleMap_injective {α V : Type*} {φ : α → V} (hφ : Function.Injective φ) :
    Function.Injective (sampleMap φ) :=
  hφ.sumMap (Sym2.map.injective hφ)

/-- Along an injective map `φ`, the weight of `φ` in the `W`-random graph driven by `ω` is the
weight of the identity in the `W`-random graph driven by the coordinates that `φ` reads. -/
private lemma homWeight_sampleGraph {α V : Type*} [Fintype α] (F : SimpleGraph α)
    [DecidableRel F.Adj] (W : ℝ → ℝ → ℝ) (ω : V ⊕ Sym2 V → ℝ) {φ : α → V}
    (hφ : Function.Injective φ) :
    homWeight F (adjWeight (sampleGraph W ω)) φ =
      homWeight F (adjWeight (sampleGraph W (ω ∘ sampleMap φ))) id := by
  classical
  unfold homWeight
  refine Finset.prod_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    simp only [adjWeight, Sym2.map_mk, id, SimpleGraph.mem_edgeSet, sampleGraph,
      SimpleGraph.fromRel_adj, Function.comp_apply, sampleMap, Sum.map_inl, Sum.map_inr,
      hφ.ne_iff]

private lemma measurable_adjWeight_sampleGraph {V : Type*} {W : ℝ → ℝ → ℝ}
    (hW : Measurable (Function.uncurry W)) (e : Sym2 V) :
    Measurable fun ω : V ⊕ Sym2 V → ℝ => adjWeight (sampleGraph W ω) e := by
  induction e using Sym2.ind with
  | _ a b =>
    have hWij (i j : V) : Measurable fun ω : V ⊕ Sym2 V → ℝ => W (ω (.inl i)) (ω (.inl j)) :=
      hW.comp (f := fun ω : V ⊕ Sym2 V → ℝ => (ω (.inl i), ω (.inl j)))
        ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
    have hlt (i j : V) : MeasurableSet
        {ω : V ⊕ Sym2 V → ℝ | ω (.inr s(i, j)) < W (ω (.inl i)) (ω (.inl j))} :=
      measurableSet_lt (measurable_pi_apply _) (hWij i j)
    have hset : MeasurableSet {ω : V ⊕ Sym2 V → ℝ | s(a, b) ∈ (sampleGraph W ω).edgeSet} := by
      simp only [SimpleGraph.mem_edgeSet, sampleGraph, SimpleGraph.fromRel_adj]
      by_cases hab : a = b
      · simp [hab]
      · simp only [ne_eq, hab, not_false_eq_true, true_and, Set.ofPred_or]
        exact (hlt a b).union (hlt b a)
    exact Measurable.ite hset measurable_const measurable_const

private lemma measurable_homWeight_sampleGraph {α V : Type*} [Fintype α] (F : SimpleGraph α)
    [DecidableRel F.Adj] {W : ℝ → ℝ → ℝ} (hW : Measurable (Function.uncurry W)) (φ : α → V) :
    Measurable fun ω : V ⊕ Sym2 V → ℝ => homWeight F (adjWeight (sampleGraph W ω)) φ :=
  Finset.measurable_prod _ fun _ _ => measurable_adjWeight_sampleGraph hW _

private lemma homWeight_mem_Icc {α V : Type*} [Fintype α] (F : SimpleGraph α)
    [DecidableRel F.Adj] (G : SimpleGraph V) [DecidableRel G.Adj] (φ : α → V) :
    homWeight F (adjWeight G) φ ∈ Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun _ _ => (adjWeight_mem_unitInterval G _).1,
    Finset.prod_le_one₀ (fun _ _ => (adjWeight_mem_unitInterval G _).1)
      fun _ _ => (adjWeight_mem_unitInterval G _).2⟩

/-- Products over the edges of a graph on `Fin k` are products over the ordered pairs `i < j` of
adjacent vertices. -/
private lemma prod_edgeFinset_eq {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
    (f : Sym2 (Fin k) → ℝ) :
    ∏ e ∈ F.edgeFinset, f e =
      ∏ i : Fin k, ∏ j : Fin k, if i < j ∧ F.Adj i j then f s(i, j) else 1 := by
  rw [← Fintype.prod_prod_type' (fun i j => if i < j ∧ F.Adj i j then f s(i, j) else 1),
    ← Finset.prod_filter]
  symm
  refine Finset.prod_nbij (fun p => s(p.1, p.2)) (fun p hp => ?_) (fun p hp q hq hpq => ?_)
    (fun e he => ?_) (fun _ _ => rfl)
  · have hp' := (Finset.mem_filter.mp hp).2
    exact SimpleGraph.mem_edgeFinset.mpr (F.mem_edgeSet.mpr hp'.2)
  · have hp' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2.1
    have hq' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2.1
    rcases Sym2.eq_iff.mp hpq with h | h
    · exact Prod.ext h.1 h.2
    · exact (lt_asymm hq' (by rw [← h.1, ← h.2]; exact hp')).elim
  · induction e using Sym2.ind with
    | _ i j =>
      have hij := F.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp (Finset.mem_coe.mp he))
      rcases lt_or_gt_of_ne hij.ne with h | h
      · exact ⟨(i, j), by simp [h, hij], rfl⟩
      · exact ⟨(j, i), by simp [h, hij.symm], Sym2.eq_swap⟩

/-- A uniform variable on `[0, 1]` falls below `c ∈ [0, 1]` with probability `c`. -/
private lemma integral_ite_lt {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    ∫ u, (if u < c then (1 : ℝ) else 0) ∂sampleMeasure = c := by
  have h : (fun u : ℝ => if u < c then (1 : ℝ) else 0) = (Iio c).indicator 1 := by
    ext u
    simp [Set.indicator, Set.mem_Iio]
  rw [h, integral_indicator_one measurableSet_Iio, measureReal_restrict_apply measurableSet_Iio]
  have h' : Iio c ∩ Icc 0 1 = Ico 0 c := by
    ext u
    simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith [hc.2]⟩
  rw [h', Real.volume_real_Ico_of_le hc.1, sub_zero]

private lemma sumPiEquivProdPi_symm_eq {ι κ : Type*} (x : ι → ℝ) (U : κ → ℝ) :
    (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ κ => ℝ).symm (x, U) = Sum.elim x U := by
  funext i
  cases i <;> rfl

/-- The expected weight of the identity map of `F` in the `W`-random graph on the vertices of `F`
is the homomorphism density `t(F, W)`: given the types `x`, the edges are independent and `ij` is
an edge with probability `W(xᵢ, xⱼ)`. -/
private lemma integral_homWeight_sampleGraph {k : ℕ} (F : SimpleGraph (Fin k))
    [DecidableRel F.Adj] {W : ℝ → ℝ → ℝ} (hW : IsGraphon W) :
    ∫ v, homWeight F (adjWeight (sampleGraph W v)) id
        ∂(Measure.pi fun _ : Fin k ⊕ Sym2 (Fin k) => sampleMeasure) =
      graphonHomDensity F W := by
  classical
  set Y : (Fin k ⊕ Sym2 (Fin k) → ℝ) → ℝ := fun v => homWeight F (adjWeight (sampleGraph W v)) id
    with hY
  have hYm : Measurable Y := measurable_homWeight_sampleGraph F hW.1 id
  set e := MeasurableEquiv.sumPiEquivProdPi fun _ : Fin k ⊕ Sym2 (Fin k) => ℝ with he
  -- the graphon's weight on an unordered pair of vertices of types `x`
  let w : (Fin k → ℝ) → Sym2 (Fin k) → ℝ := fun x =>
    Sym2.lift ⟨fun a b => W (x a) (x b), fun a b => hW.2.1 _ _⟩
  have hw (x : Fin k → ℝ) (z : Sym2 (Fin k)) : w x z ∈ Icc (0 : ℝ) 1 := by
    induction z using Sym2.ind with
    | _ a b => exact hW.2.2 _ _
  -- given the types, the edges are independent with probabilities `w x z`
  have hinner (x : Fin k → ℝ) :
      ∫ U, Y (e.symm (x, U)) ∂(Measure.pi fun _ : Sym2 (Fin k) => sampleMeasure) =
        ∏ z ∈ F.edgeFinset, w x z := by
    have hfac (U : Sym2 (Fin k) → ℝ) : Y (e.symm (x, U)) =
        ∏ z, if z ∈ F.edgeFinset then (if U z < w x z then 1 else 0) else 1 := by
      rw [Fintype.prod_ite_mem, he, sumPiEquivProdPi_symm_eq, hY]
      dsimp only [homWeight]
      refine Finset.prod_congr rfl fun z hz => ?_
      induction z using Sym2.ind with
      | _ a b =>
        have hab : a ≠ b := F.ne_of_adj (F.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp hz))
        simp [adjWeight, sampleGraph, hab, w, Sym2.eq_swap, hW.2.1 (x b) (x a)]
        split_ifs with h <;> simp [h]
    simp_rw [hfac]
    refine (integral_fintype_prod_eq_prod
      (fun z u => if z ∈ F.edgeFinset then (if u < w x z then (1 : ℝ) else 0) else 1)).trans ?_
    rw [← Fintype.prod_ite_mem F.edgeFinset (w x)]
    refine Fintype.prod_congr _ _ fun z => ?_
    split_ifs with hz
    · exact integral_ite_lt (hw x z)
    · simp
  have hint : Integrable (fun p => Y (e.symm p))
      ((Measure.pi fun _ : Fin k => sampleMeasure).prod
        (Measure.pi fun _ : Sym2 (Fin k) => sampleMeasure)) := by
    refine Integrable.of_bound (hYm.comp e.symm.measurable).aestronglyMeasurable 1
      (ae_of_all _ fun p => ?_)
    have := homWeight_mem_Icc F (sampleGraph W (e.symm p)) id
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [this.1], this.2⟩
  rw [← (measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin k ⊕ Sym2 (Fin k) => sampleMeasure)).integral_comp' Y, integral_prod _ hint]
  simp_rw [hinner]
  rw [graphonHomDensity, volume_pi, Measure.restrict_pi_pi]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [prod_edgeFinset_eq]
  rfl

private lemma integrable_of_mem_Icc {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    {a b : ℝ} (hab : ∀ x, f x ∈ Icc a b) :
    Integrable f (Measure.pi fun _ : ι => sampleMeasure) :=
  Integrable.of_bound hf.aestronglyMeasurable (max |a| |b|) (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [(hab x).1, neg_abs_le a, le_max_left |a| |b|]
    · linarith [(hab x).2, le_abs_self b, le_max_right |a| |b|])

private lemma graphonHomDensity_mem_Icc {k : ℕ} (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
    {W : ℝ → ℝ → ℝ} (hW : IsGraphon W) : graphonHomDensity F W ∈ Icc (0 : ℝ) 1 := by
  have hint := integrable_of_mem_Icc (ι := Fin k ⊕ Sym2 (Fin k))
    (measurable_homWeight_sampleGraph F hW.1 id) fun v => homWeight_mem_Icc F (sampleGraph W v) id
  rw [← integral_homWeight_sampleGraph F hW]
  constructor
  · exact integral_nonneg fun v => (homWeight_mem_Icc F _ id).1
  · calc _ ≤ ∫ _v, (1 : ℝ) ∂(Measure.pi fun _ : Fin k ⊕ Sym2 (Fin k) => sampleMeasure) :=
          integral_mono hint (integrable_const 1) fun v => (homWeight_mem_Icc F _ id).2
      _ = 1 := by simp

/-- Two injective maps with disjoint images read disjoint sets of coordinates of the sample, so
their centred weights are uncorrelated. -/
private lemma integral_centred_mul_eq_zero {n k : ℕ} (F : SimpleGraph (Fin k))
    [DecidableRel F.Adj] {W : ℝ → ℝ → ℝ} (hW : IsGraphon W) {φ ψ : Fin k → Fin n}
    (hφψ : Function.Injective (Sum.elim φ ψ)) :
    ∫ ω, (homWeight F (adjWeight (sampleGraph W ω)) φ - graphonHomDensity F W) *
        (homWeight F (adjWeight (sampleGraph W ω)) ψ - graphonHomDensity F W)
        ∂(Measure.pi fun _ : Fin n ⊕ Sym2 (Fin n) => sampleMeasure) = 0 := by
  obtain ⟨hφ, hψ, hne⟩ := Sum.elim_injective.mp hφψ
  set τ := graphonHomDensity F W with hτ
  set Y : (Fin k ⊕ Sym2 (Fin k) → ℝ) → ℝ := fun v => homWeight F (adjWeight (sampleGraph W v)) id
  have hYm : Measurable Y := measurable_homWeight_sampleGraph F hW.1 id
  have hYint : Integrable Y (Measure.pi fun _ : Fin k ⊕ Sym2 (Fin k) => sampleMeasure) :=
    integrable_of_mem_Icc hYm fun v => homWeight_mem_Icc F (sampleGraph W v) id
  have hYτ : ∫ v, (Y v - τ) ∂(Measure.pi fun _ : Fin k ⊕ Sym2 (Fin k) => sampleMeasure) = 0 := by
    rw [integral_sub hYint (integrable_const τ), integral_homWeight_sampleGraph F hW]
    simp [hτ]
  -- the coordinates read by the pair `(φ, ψ)`
  set J := Sum.elim (sampleMap φ) (sampleMap ψ)
  have hJinj : Function.Injective J := by
    refine Sum.elim_injective.mpr ⟨sampleMap_injective hφ, sampleMap_injective hψ, ?_⟩
    rintro (a | z) (b | z')
    · simpa [sampleMap] using hne a b
    · simp [sampleMap]
    · simp [sampleMap]
    · simp only [sampleMap, Sum.map_inr, ne_eq, Sum.inr.injEq]
      intro h
      induction z using Sym2.ind with
      | _ a a' =>
        have : φ a ∈ Sym2.map ψ z' := h ▸ Sym2.mem_map.mpr ⟨a, Sym2.mem_mk_left a a', rfl⟩
        obtain ⟨b, -, hb⟩ := Sym2.mem_map.mp this
        exact hne a b hb.symm
  set H : ((Fin k ⊕ Sym2 (Fin k)) ⊕ (Fin k ⊕ Sym2 (Fin k)) → ℝ) → ℝ :=
    fun v => (Y (v ∘ Sum.inl) - τ) * (Y (v ∘ Sum.inr) - τ)
  have hHm : Measurable H :=
    ((hYm.comp (measurePreserving_comp Sum.inl_injective).measurable).sub measurable_const).mul
      ((hYm.comp (measurePreserving_comp Sum.inr_injective).measurable).sub measurable_const)
  have hpoint (ω : Fin n ⊕ Sym2 (Fin n) → ℝ) :
      (homWeight F (adjWeight (sampleGraph W ω)) φ - τ) *
        (homWeight F (adjWeight (sampleGraph W ω)) ψ - τ) = H (ω ∘ J) := by
    rw [homWeight_sampleGraph F W ω hφ, homWeight_sampleGraph F W ω hψ]
    rfl
  simp_rw [hpoint]
  have hmp := measurePreserving_comp (ι := Fin n ⊕ Sym2 (Fin n)) hJinj
  rw [← integral_map hmp.measurable.aemeasurable hHm.aestronglyMeasurable, hmp.map_eq,
    ← (measurePreserving_sumPiEquivProdPi_symm
      (fun _ : (Fin k ⊕ Sym2 (Fin k)) ⊕ (Fin k ⊕ Sym2 (Fin k)) => sampleMeasure)).integral_comp' H]
  have hfactor (z : (Fin k ⊕ Sym2 (Fin k) → ℝ) × (Fin k ⊕ Sym2 (Fin k) → ℝ)) :
      H ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm z) = (Y z.1 - τ) * (Y z.2 - τ) :=
    rfl
  simp_rw [hfactor]
  rw [integral_prod_mul (fun a => Y a - τ) (fun b => Y b - τ), hYτ, zero_mul]

/-- At most a `|β|² / n` fraction of the maps `β → Fin n` are not injective: two given points
`a ≠ b` have the same image under exactly `n ^ (|β| - 1)` maps. -/
private lemma sum_not_injective_mul_le {β : Type*} [Fintype β] [DecidableEq β] (n : ℕ) :
    (∑ f : β → Fin n, if Function.Injective f then (0 : ℝ) else 1) * n ≤
      (Fintype.card β : ℝ) ^ 2 * (n : ℝ) ^ Fintype.card β := by
  set c : (β → Fin n) → β → β → ℝ := fun f a b => if a ≠ b ∧ f a = f b then 1 else 0 with hc
  have hc0 (f : β → Fin n) (a b : β) : 0 ≤ c f a b := by
    simp only [hc]
    split_ifs <;> norm_num
  have h1 (f : β → Fin n) : (if Function.Injective f then (0 : ℝ) else 1) ≤ ∑ a, ∑ b, c f a b := by
    split_ifs with hf
    · exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hc0 f a b
    · obtain ⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by
        simpa [Function.Injective] using hf
      calc (1 : ℝ) = c f a b := by simp [hc, hab, hne]
        _ ≤ ∑ b', c f a b' := Finset.single_le_sum (fun b' _ => hc0 f a b') (Finset.mem_univ b)
        _ ≤ ∑ a', ∑ b', c f a' b' :=
          Finset.single_le_sum (f := fun a' => ∑ b', c f a' b')
            (fun a' _ => Finset.sum_nonneg fun b' _ => hc0 f a' b') (Finset.mem_univ a)
  have h2 (a b : β) : (∑ f : β → Fin n, c f a b) * n ≤ (n : ℝ) ^ Fintype.card β := by
    by_cases hab : a = b
    · simp [hc, hab]
    · have key := sum_sum_update (V := Fin n)
        (fun f : β → Fin n => if f a = f b then (1 : ℝ) else 0) b
      have hupd (f : β → Fin n) : ∑ y : Fin n,
          (if Function.update f b y a = Function.update f b y b then (1 : ℝ) else 0) = 1 := by
        simp [Function.update_of_ne hab]
      simp only [hupd, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, mul_one] at key
      have hcab : (∑ f : β → Fin n, c f a b) = ∑ f : β → Fin n, if f a = f b then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl fun f _ => by simp [hc, hab]
      rw [hcab, mul_comm]
      exact_mod_cast key.symm.le
  calc (∑ f : β → Fin n, if Function.Injective f then (0 : ℝ) else 1) * n
      ≤ (∑ f : β → Fin n, ∑ a, ∑ b, c f a b) * n :=
        mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun f _ => h1 f) (Nat.cast_nonneg n)
    _ = ∑ a, ∑ b, (∑ f : β → Fin n, c f a b) * n := by
        rw [Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm, Finset.sum_mul]
    _ ≤ ∑ _a : β, ∑ _b : β, (n : ℝ) ^ Fintype.card β :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h2 a b
    _ = (Fintype.card β : ℝ) ^ 2 * (n : ℝ) ^ Fintype.card β := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

private lemma measurable_homDensity_sampleGraph {α V : Type*} [Fintype α] [DecidableEq α]
    [Fintype V] (F : SimpleGraph α) [DecidableRel F.Adj] {W : ℝ → ℝ → ℝ}
    (hW : Measurable (Function.uncurry W)) :
    Measurable fun ω : V ⊕ Sym2 V → ℝ => homDensity F (adjWeight (sampleGraph W ω)) :=
  (Finset.measurable_sum _ fun φ _ => measurable_homWeight_sampleGraph F hW φ).div_const _

/-- **Second moment bound.** The density of `F` in the `W`-random graph on `n` vertices has mean
square deviation at most `(2k)² / n` from `t(F, W)`. -/
private lemma integral_sq_sub_le {n k : ℕ} (hn : 0 < n) (F : SimpleGraph (Fin k))
    [DecidableRel F.Adj] {W : ℝ → ℝ → ℝ} (hW : IsGraphon W) :
    ∫ ω, (homDensity F (adjWeight (sampleGraph W ω)) - graphonHomDensity F W) ^ 2
        ∂(Measure.pi fun _ : Fin n ⊕ Sym2 (Fin n) => sampleMeasure) ≤ (2 * k : ℝ) ^ 2 / n := by
  set μ := Measure.pi fun _ : Fin n ⊕ Sym2 (Fin n) => sampleMeasure
  set τ := graphonHomDensity F W
  set X : (Fin k → Fin n) → (Fin n ⊕ Sym2 (Fin n) → ℝ) → ℝ :=
    fun φ ω => homWeight F (adjWeight (sampleGraph W ω)) φ
  have hτ01 : τ ∈ Icc (0 : ℝ) 1 := graphonHomDensity_mem_Icc F hW
  have hXm (φ : Fin k → Fin n) : Measurable (X φ) := measurable_homWeight_sampleGraph F hW.1 φ
  have hX01 (φ : Fin k → Fin n) (ω) : X φ ω ∈ Icc (0 : ℝ) 1 := homWeight_mem_Icc F _ φ
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnk : (0 : ℝ) < (n : ℝ) ^ k := pow_pos hn' k
  -- the density is the average weight of a map `Fin k → Fin n`
  have hD (ω) : homDensity F (adjWeight (sampleGraph W ω)) - τ =
      (∑ φ, (X φ ω - τ)) / (n : ℝ) ^ k := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, homDensity, Fintype.card_fin,
      Fintype.card_fin]
    field_simp
    push_cast
    ring
  have hsq (ω) : (homDensity F (adjWeight (sampleGraph W ω)) - τ) ^ 2 =
      (∑ φ, ∑ ψ, (X φ ω - τ) * (X ψ ω - τ)) / ((n : ℝ) ^ k) ^ 2 := by
    rw [hD, div_pow, sq, Fintype.sum_mul_sum]
  have hcentred (φ : Fin k → Fin n) (ω) : |X φ ω - τ| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(hX01 φ ω).1, hτ01.2], by linarith [(hX01 φ ω).2, hτ01.1]⟩
  have hprod (φ ψ : Fin k → Fin n) (ω) : |(X φ ω - τ) * (X ψ ω - τ)| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul (hcentred φ ω) (hcentred ψ ω) (abs_nonneg _) zero_le_one
  have hint (φ ψ : Fin k → Fin n) : Integrable (fun ω => (X φ ω - τ) * (X ψ ω - τ)) μ := by
    refine integrable_of_mem_Icc (((hXm φ).sub measurable_const).mul
      ((hXm ψ).sub measurable_const)) (a := -1) (b := 1) fun ω => ?_
    rw [mem_Icc, ← abs_le]
    exact hprod φ ψ ω
  -- a pair contributes at most `1`, and nothing when it is injective
  have hpair (φ ψ : Fin k → Fin n) : ∫ ω, (X φ ω - τ) * (X ψ ω - τ) ∂μ ≤
      if Function.Injective (Sum.elim φ ψ) then 0 else 1 := by
    split_ifs with h
    · exact (integral_centred_mul_eq_zero F hW h).le
    · calc _ ≤ ∫ _ω, (1 : ℝ) ∂μ := integral_mono (hint φ ψ) (integrable_const 1) fun ω =>
            (le_abs_self _).trans (hprod φ ψ ω)
        _ = 1 := by simp
  have hsum : ∑ φ : Fin k → Fin n, ∑ ψ : Fin k → Fin n,
      (if Function.Injective (Sum.elim φ ψ) then (0 : ℝ) else 1) =
        ∑ f : Fin k ⊕ Fin k → Fin n, if Function.Injective f then (0 : ℝ) else 1 := by
    rw [← Fintype.sum_prod_type']
    exact Equiv.sum_comp (Equiv.sumArrowEquivProdArrow _ _ _).symm
      (fun f => if Function.Injective f then (0 : ℝ) else 1)
  have hcount := sum_not_injective_mul_le (β := Fin k ⊕ Fin k) n
  rw [Fintype.card_sum, Fintype.card_fin] at hcount
  simp_rw [hsq]
  rw [integral_div, integral_finsetSum _ fun φ _ => integrable_finsetSum _ fun ψ _ => hint φ ψ]
  rw [Finset.sum_congr rfl fun φ _ => integral_finsetSum _ fun ψ _ => hint φ ψ]
  calc (∑ φ, ∑ ψ, ∫ ω, (X φ ω - τ) * (X ψ ω - τ) ∂μ) / ((n : ℝ) ^ k) ^ 2
      ≤ (∑ φ : Fin k → Fin n, ∑ ψ : Fin k → Fin n,
          (if Function.Injective (Sum.elim φ ψ) then (0 : ℝ) else 1)) / ((n : ℝ) ^ k) ^ 2 := by
        gcongr with φ _ ψ _
        exact hpair φ ψ
    _ ≤ (2 * k : ℝ) ^ 2 / n := by
        rw [hsum, div_le_div_iff₀ (by positivity) hn']
        calc (∑ f : Fin k ⊕ Fin k → Fin n, if Function.Injective f then (0 : ℝ) else 1) * n
            ≤ ((k + k : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ (k + k) := hcount
          _ = (2 * k : ℝ) ^ 2 * ((n : ℝ) ^ k) ^ 2 := by push_cast; ring

/-- For every `m` there is a sample on finitely many vertices whose `W`-random graph has, for
every graph `F` on at most `m` vertices, density within `1 / (m + 1)` of `t(F, W)`: the mean of the
sum of the squared errors over these finitely many graphs tends to `0` (first moment method). -/
private lemma exists_sample_close {W : ℝ → ℝ → ℝ} (hW : IsGraphon W) (m : ℕ) :
    ∃ n, 0 < n ∧ ∃ ω : Fin n ⊕ Sym2 (Fin n) → ℝ, ∀ k ≤ m, ∀ (F : SimpleGraph (Fin k))
      [DecidableRel F.Adj],
      |homDensity F (adjWeight (sampleGraph W ω)) - graphonHomDensity F W| < 1 / (m + 1) := by
  obtain ⟨C, hC0, hCdef⟩ : ∃ C : ℝ, 0 ≤ C ∧
      C = ∑ k ∈ Finset.range (m + 1), (Fintype.card (SimpleGraph (Fin k)) : ℝ) :=
    ⟨_, Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _, rfl⟩
  obtain ⟨n, hnpos, hn⟩ : ∃ n : ℕ, 0 < n ∧ 4 * (m : ℝ) ^ 2 * C * (m + 1) ^ 2 < n :=
    ⟨⌈4 * (m : ℝ) ^ 2 * C * (m + 1) ^ 2⌉₊ + 1, Nat.succ_pos _, by
      push_cast
      linarith [Nat.le_ceil (4 * (m : ℝ) ^ 2 * C * (m + 1) ^ 2)]⟩
  set μ := Measure.pi fun _ : Fin n ⊕ Sym2 (Fin n) => sampleMeasure
  -- squared errors, for the classical decidability instances
  set err : ∀ k, SimpleGraph (Fin k) → (Fin n ⊕ Sym2 (Fin n) → ℝ) → ℝ := fun k F ω =>
    (@homDensity (Fin k) (Fin n) _ _ _ F (Classical.decRel F.Adj)
      (adjWeight (sampleGraph W ω)) - @graphonHomDensity k F (Classical.decRel F.Adj) W) ^ 2
    with herr
  have hint (k : ℕ) (F : SimpleGraph (Fin k)) : Integrable (err k F) μ := by
    let _ := Classical.decRel F.Adj
    refine integrable_of_mem_Icc
      (((measurable_homDensity_sampleGraph F hW.1).sub measurable_const).pow_const 2)
      (a := 0) (b := 1) fun ω => ⟨sq_nonneg _, ?_⟩
    have h1 := homDensity_nonneg F (w := adjWeight (sampleGraph W ω))
      fun z => (adjWeight_mem_unitInterval _ z).1
    have h2 := homDensity_le_one F (w := adjWeight (sampleGraph W ω))
      (adjWeight_mem_unitInterval _)
    have h3 := graphonHomDensity_mem_Icc F hW
    rw [sq_le_one_iff_abs_le_one, abs_le]
    constructor <;> linarith [h3.1, h3.2]
  set Φ : (Fin n ⊕ Sym2 (Fin n) → ℝ) → ℝ := fun ω =>
    ∑ k ∈ Finset.range (m + 1), ∑ F : SimpleGraph (Fin k), err k F ω
  have hΦint : Integrable Φ μ :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun F _ => hint k F
  have hΦ : ∫ ω, Φ ω ∂μ < 1 / ((m : ℝ) + 1) ^ 2 := by
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun F _ => hint k F]
    calc ∑ k ∈ Finset.range (m + 1), ∫ ω, ∑ F : SimpleGraph (Fin k), err k F ω ∂μ
        = ∑ k ∈ Finset.range (m + 1), ∑ F : SimpleGraph (Fin k), ∫ ω, err k F ω ∂μ :=
          Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun F _ => hint k F
      _ ≤ ∑ k ∈ Finset.range (m + 1), ∑ _F : SimpleGraph (Fin k), (2 * m : ℝ) ^ 2 / n := by
          refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun F _ => ?_
          have hkm : (k : ℝ) ≤ m := by
            exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          calc ∫ ω, err k F ω ∂μ ≤ (2 * k : ℝ) ^ 2 / n :=
                @integral_sq_sub_le n k hnpos F (Classical.decRel F.Adj) W hW
            _ ≤ (2 * m : ℝ) ^ 2 / n := by gcongr
      _ = C * (2 * m : ℝ) ^ 2 / n := by
          rw [hCdef, Finset.sum_mul, Finset.sum_div]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ < 1 / ((m : ℝ) + 1) ^ 2 := by
          rw [div_lt_div_iff₀ (Nat.cast_pos.mpr hnpos) (by positivity)]
          have : C * (2 * m : ℝ) ^ 2 * (m + 1) ^ 2 = 4 * (m : ℝ) ^ 2 * C * (m + 1) ^ 2 := by ring
          linarith
  obtain ⟨ω, hω⟩ := exists_le_integral hΦint
  refine ⟨n, hnpos, ω, fun k hk F inst => ?_⟩
  obtain rfl : inst = Classical.decRel F.Adj := Subsingleton.elim _ _
  have h1 : err k F ω ≤ Φ ω := by
    have hk' : k ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    refine (Finset.single_le_sum (f := fun F => err k F ω) (fun F _ => sq_nonneg _)
      (Finset.mem_univ F)).trans ?_
    exact Finset.single_le_sum (f := fun k => ∑ F : SimpleGraph (Fin k), err k F ω)
      (fun k _ => Finset.sum_nonneg fun F _ => sq_nonneg _) hk'
  have h2 : err k F ω < (1 / ((m : ℝ) + 1)) ^ 2 := by
    rw [div_pow, one_pow]
    exact h1.trans_lt (hω.trans_lt hΦ)
  simp only [herr] at h2
  exact abs_lt_of_sq_lt_sq h2 (by positivity)

/-- **Every graphon is a graph limit.** For every graphon `W` there is a sequence of nonempty simple
graphs `Gₙ` with `t(F, Gₙ) → t(F, W)` for every simple graph `F` (Lovász–Szegedy, *Limits of dense
graph sequences* (2006), Theorem 2.2, (b) ⇒ (a), via Corollary 2.6 on `W`-random graphs;
Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense graphs I* (2008),
Theorem 3.1). -/
public theorem exists_graph_sequence_tendsto {W : ℝ → ℝ → ℝ} (hW : IsGraphon W) :
    ∃ (N : ℕ → ℕ) (G : ∀ n, SimpleGraph (Fin (N n))) (_ : ∀ n, DecidableRel (G n).Adj),
      (∀ n, 0 < N n) ∧ ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj],
        Tendsto (fun n => homDensity F (adjWeight (G n))) atTop (𝓝 (graphonHomDensity F W)) := by
  choose N hN ω hω using exists_sample_close hW
  refine ⟨N, fun m => sampleGraph W (ω m), fun m => inferInstance, hN, fun k F _ => ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _)
    ((eventually_ge_atTop k).mono fun m hm => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Real.norm_eq_abs]
  exact (hω m k hm F).le

end MathlibExt.Combinatorics.SimpleGraph.GraphLimitsWanted
