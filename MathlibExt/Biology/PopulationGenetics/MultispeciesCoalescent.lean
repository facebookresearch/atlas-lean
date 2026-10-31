/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Topology
public import MathlibExt.Biology.PopulationGenetics.Coalescent.BlockCounting
public import MathlibExt.Biology.Phylogenetics.TreeCount
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Matrix.Normed

/-!
# The multispecies coalescent: concordance, the anomaly zone, quartets, clades

The **multispecies coalescent** models gene genealogies inside a species tree: each branch of
the species tree is a population in which the gene lineages present run Kingman's coalescent
for the length of the branch (in coalescent units of `2N` generations); at a speciation vertex
the lineages of the two daughter populations enter the ancestral population; in the root
population all remaining lineages coalesce. We sample one gene lineage per species.

We build the law of the gene tree from merged ingredients (`geneTreeProb`): along a branch of
length `t` the number of lineages goes from `m` to `j` with Tavaré's probability
`tavareProb m j t`, and, independently of the coalescence times, the order of the
coalescences is random joining (`randomJoining`), as in Pamilo & Nei (1988) and Degnan &
Salter (2005). A gene tree is recorded by its set of clusters (the sets of genes below its
vertices). Expectations under random joining are averages over ranked histories, so the
random-joining factors of the statements below are computed exactly by kernel evaluation.

* **Three species** (Hudson 1983; Pamilo & Nei 1988): with internal branch `t`, the gene tree
  matches the species tree with probability `1 - (2/3) e^{-t}`, and each of the two other
  gene trees has probability `(1/3) e^{-t}`; there are no anomalous gene trees.
* **Four species, the anomaly zone** (Degnan & Rosenberg 2006): on the caterpillar species
  tree `(((A, B), C), D)` with deeper internal branch `x` and shallower internal branch `y`,
  the gene trees `(((A, B), C), D)`, `((A, C), (B, D))`, `((A, D), (B, C))` and
  `((A, B), (C, D))` have the probabilities `f`, `g`, `g`, `h` of the paper's equations
  (1)–(3); `((A, B), (C, D))` is more probable than the matching tree iff `y < a(x)`, and
  `((A, C), (B, D))` is iff `y < b(x)` (equations (4), (5)), with `b(0) = log (7/6)`. No
  asymmetric gene tree is ever more probable than the matching one, so the species tree has an
  anomalous gene tree iff `y < a(x)`; the balanced four-species tree has none.
* **Unrooted quartets** (Allman, Degnan & Rhodes 2011): on both four-species shapes, the
  unrooted gene quartet matches the species quartet with probability `1 - (2/3) e^{-t}`,
  `t` the internal edge of the unrooted species quartet, and each other quartet has
  probability `(1/3) e^{-t}`; so the species quartet is the most probable. This is the
  four-species fact behind the statistical consistency of quartet-based methods such as ASTRAL
  (Mirarab et al. 2014); consistency on `n` species is not formalized here.
* **Clade probabilities** (Rosenberg 2003): under random joining a fixed set of `k` among
  `m` genes is a clade with probability `2m / (k (k + 1) C(m, k))`, proved here for `m ≤ 5`.

## Main results

* `SpeciesTree`, `exitLaw`, `branchStep`, `geneTreeProb`: the multispecies coalescent;
  `geneTreeProb_true`: it is a probability law, using `sum_tavareProb` (Tavaré's
  probabilities from `m ≥ 1` lineages sum to one).
* `geneTreeProb_triple_matching`, `geneTreeProb_triple_cherry_02`, `geneTreeProb_triple_cherry_12`,
  `triple_no_anomaly`: three species.
* `geneTreeProb_caterpillar_matching`, `geneTreeProb_caterpillar_AC_BD`,
  `geneTreeProb_caterpillar_AD_BC`, `geneTreeProb_caterpillar_AB_CD`: Degnan & Rosenberg's
  `f`, `g`, `g`, `h`.
* `drF_lt_drH_iff`, `drF_lt_drG_iff`, `drG_lt_drH`, `anomalyB_zero`, `tendsto_anomalyA`,
  `caterpillar_anomalous_iff`, `caterpillar_anomalous_AC_BD_iff`, `caterpillar_le_matching`,
  `caterpillar_exists_anomalous_iff`, `balanced_no_anomaly`: the anomaly zone.
* `geneTreeProb_caterpillar_split_01`, `geneTreeProb_balanced_split_01` (and the discordant
  splits), `split_01_most_probable`: unrooted quartets.
* `randomJoining_isClade_of_le_five`: Rosenberg's clade probability for `m ≤ 5`.

Not covered: gene trees on more than four species (the definition handles any species tree, but
only the trees above are evaluated), in particular Degnan & Rosenberg's anomalies for five or
more species; quartet concordance for every labeling of the leaves and for quartets inside
larger species trees, hence ASTRAL's statistical consistency on `n` species; the clade
probability for `m > 5` (stated in `MultispeciesCoalescentWanted`). The independence of the
jump chain of Kingman's coalescent from its holding times, which justifies `branchStep`, is
part of the model and is not derived here.

## References

* R. R. Hudson, "Testing the constant-rate neutral allele model with protein sequence data",
  Evolution 37 (1983) 203–217.
* P. Pamilo and M. Nei, "Relationships between gene trees and species trees", Mol. Biol.
  Evol. 5 (1988) 568–583.
* J. H. Degnan and L. A. Salter, "Gene tree distributions under the coalescent process",
  Evolution 59 (2005) 24–37.
* J. H. Degnan and N. A. Rosenberg, "Discordance of species trees with their most likely gene
  trees", PLoS Genet. 2 (2006) e68.
* N. A. Rosenberg, "The shapes of neutral gene genealogies in two species: probabilities of
  monophyly, paraphyly, and polyphyly in a coalescent model", Evolution 57 (2003) 1465–1477.
* E. S. Allman, J. H. Degnan and J. A. Rhodes, "Identifying the rooted species tree from the
  distribution of unrooted gene trees under the coalescent", J. Math. Biol. 62 (2011)
  833–862.
* S. Mirarab, R. Reaz, Md. S. Bayzid, T. Zimmermann, M. S. Swenson and T. Warnow, "ASTRAL:
  genome-scale coalescent-based species tree estimation", Bioinformatics 30 (2014)
  i541–i548.
-/

@[expose] public section

open MeasureTheory Finset Filter Topology
open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCounting
open Matrix

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescent

/-! ### Species trees -/

/-- A rooted binary **species tree** on the species `Fin n` with branch lengths: `leaf i` is
species `i`, and `node l r t` is the ancestral species of the species below `l` and `r`, where
`t` is the length, in coalescent units (`2N` generations), of the branch above the node, i.e.
the time during which the ancestral population of `l` and `r` exists before it merges with a
sister population. The length stored at the root node is not used: the root population lasts
until all lineages have coalesced. Leaf branch lengths are not recorded, because one gene
lineage is sampled per species and a single lineage cannot coalesce. A species tree on the
species `Fin n` labels each species by exactly one leaf; the type does not enforce this, and
the theorems below are about concrete trees with this property. -/
inductive SpeciesTree (n : ℕ) where
  /-- The species `i`. -/
  | leaf : Fin n → SpeciesTree n
  /-- The ancestor of `l` and `r`, with branch length `t` above it. -/
  | node : SpeciesTree n → SpeciesTree n → ℝ → SpeciesTree n

namespace SpeciesTree

variable {n : ℕ}

/-- The species below a node. -/
def taxa : SpeciesTree n → Finset (Fin n)
  | leaf i => {i}
  | node l r _ => l.taxa ∪ r.taxa

/-- The clusters (clades) of a species tree: the sets of species below its vertices, including
the singletons and the full set of species. -/
def clusters : SpeciesTree n → Finset (Finset (Fin n))
  | leaf i => {{i}}
  | node l r _ => insert (l.taxa ∪ r.taxa) (l.clusters ∪ r.clusters)

/-- The topology of a species tree, forgetting branch lengths, as a planar rooted binary tree. -/
def shape : SpeciesTree n → MathlibExt.Biology.Phylogenetics.TreeCount.PlaneTree (Fin n)
  | leaf i => .leaf i
  | node l r _ => .node l.shape r.shape

end SpeciesTree

open SpeciesTree

/-! ### Tavaré's probabilities sum to one -/

private theorem exp_mulVec_of_mulVec_eq_zero {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ)
    (h : A *ᵥ v = 0) : NormedSpace.exp A *ᵥ v = v := by
  let _ := Matrix.linftyOpNormedRing (n := Fin k) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := Fin k) (R := ℝ) (α := ℝ)
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have hc : Continuous fun B : Matrix (Fin k) (Fin k) ℝ => B *ᵥ v :=
    Continuous.matrix_mulVec continuous_id continuous_const
  have hm := hs.map (Matrix.mulVec.addMonoidHomLeft v) hc
  have h1 : HasSum (fun n : ℕ => (Matrix.mulVec.addMonoidHomLeft v)
      ((n.factorial⁻¹ : ℝ) • A ^ n)) v := by
    convert hasSum_single (f := fun n : ℕ => (Matrix.mulVec.addMonoidHomLeft v)
      ((n.factorial⁻¹ : ℝ) • A ^ n)) 0 ?_ using 1
    · simp [Matrix.mulVec.addMonoidHomLeft]
    · intro n hn
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp [Matrix.mulVec.addMonoidHomLeft, pow_succ, ← Matrix.mulVec_mulVec, h,
        Matrix.smul_mulVec]
  exact hm.unique h1

private theorem blockCountingGenerator_mulVec (n : ℕ) :
    blockCountingGenerator n *ᵥ (fun j => if (j : ℕ) = 0 then 0 else 1) = 0 := by
  funext k
  simp only [Matrix.mulVec, dotProduct, blockCountingGenerator, Matrix.of_apply, Pi.zero_apply]
  by_cases hk : (k : ℕ) ≤ 1
  · have h0 : ((k : ℕ).choose 2 : ℝ) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    simp [h0]
  · have hk1 : (k : ℕ) - 1 < n + 1 := by omega
    rw [Fintype.sum_eq_add (⟨(k : ℕ) - 1, hk1⟩ : Fin (n + 1)) k]
    · simp only [show (k : ℕ) - 1 + 1 = k by omega, ite_true]
      simp only [ite_false, show (k : ℕ) ≠ 0 by omega, show (k : ℕ) - 1 ≠ 0 by omega,
        show (k : ℕ) + 1 ≠ k by omega]
      ring
    · intro h; rw [Fin.ext_iff] at h; simp at h; omega
    · intro j hj
      have h1 : (j : ℕ) + 1 ≠ k := fun h => hj.1 (Fin.ext (by simp; omega))
      simp [h1, hj.2]

/-- **Tavaré's probabilities sum to one**: from `m ≥ 1` lineages, the number of ancestors at
time `t` is one of `1, …, m`. (The rows of `exp (t • G)` restricted to the states `≥ 1` sum to
one because `G` kills the indicator of `{1, …, n}`; an identity for every real `t`.) -/
theorem sum_tavareProb {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    ∑ j ∈ Finset.Icc 1 m, tavareProb m j t = 1 := by
  set v : Fin (m + 1) → ℝ := fun j => if (j : ℕ) = 0 then 0 else 1
  have hv : NormedSpace.exp (t • blockCountingGenerator m) *ᵥ v = v :=
    exp_mulVec_of_mulVec_eq_zero _ v (by
      rw [Matrix.smul_mulVec, blockCountingGenerator_mulVec, smul_zero])
  have hi := congrFun hv (Fin.last m)
  simp only [Matrix.mulVec, dotProduct, v, Fin.val_last, show m ≠ 0 by omega, ite_false] at hi
  have hterm : ∀ j : Fin (m + 1),
      (NormedSpace.exp (t • blockCountingGenerator m) (Fin.last m) j *
        if (j : ℕ) = 0 then 0 else 1) = if (j : ℕ) = 0 then 0 else tavareProb m j t := by
    intro j
    split_ifs with h
    · simp
    · rw [exp_blockCountingGenerator_apply m t _ _ (by omega) (Fin.le_last j), Fin.val_last,
        mul_one]
  rw [Finset.sum_congr rfl (fun j _ => hterm j),
    Fin.sum_univ_eq_sum_range (fun j => if j = 0 then 0 else tavareProb m j t),
    Finset.sum_range_succ'] at hi
  have hI : Finset.Icc 1 m = (Finset.range m).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨j - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; omega
  rw [hI, Finset.sum_map, ← hi]
  simp

/-! ### Coalescence inside one population -/

variable {n : ℕ}

/-- The lineages after the first `t` coalescence events of the ranked history `h` (of `m`
lineages), starting from the lineages `bs`, each given as the set of sampled genes it is
ancestral to. Events follow the encoding of `RankedHistory`: the pair `{a, b}` with `a < b`
merges into position `a`, and position `b` is removed (`mergeBlocks`). With the singletons as
starting lineages this is `blocksAfter` (`mergeAlong_singletons`). -/
def mergeAlong {m : ℕ} (bs : List (Finset (Fin n))) (h : RankedHistory m) (t : ℕ) :
    List (Finset (Fin n)) :=
  ((List.finRange (m - 1)).take t).foldl
    (fun bs i =>
      let s : Finset ℕ := (h i).1.map Fin.valEmbedding
      mergeBlocks bs (s.min.getD 0) (s.max.getD 0))
    bs

/-- Starting from the singletons, `mergeAlong` is `blocksAfter`. -/
theorem mergeAlong_singletons (h : RankedHistory n) (t : ℕ) :
    mergeAlong ((List.finRange n).map fun j => {j}) h t = blocksAfter h t :=
  rfl

/-- The clusters formed during the first `t` coalescence events of `h` from the lineages `bs`:
every lineage present at some step `u ≤ t`, as the set of sampled genes it is ancestral to. -/
def cladesAlong {m : ℕ} (bs : List (Finset (Fin n))) (h : RankedHistory m) (t : ℕ) :
    Finset (Finset (Fin n)) :=
  (range (t + 1)).biUnion fun u => (mergeAlong bs h u).toFinset

/-! ### The multispecies coalescent -/

/-- One population of the multispecies coalescent along a branch of length `t`. It receives
`m` lineages `bs` (and the clusters `acc` formed below it). Under Kingman's coalescent the
number `j` of lineages left at the top of the branch has law `tavareProb m j t` (Tavaré's
formula, `exp_blockCountingGenerator_apply`), and, independently of the coalescence times, the
order of the `m - j` coalescences is the beginning of a random-joining history of the `m`
lineages (`randomJoining`). The continuation `k` receives the number of exiting lineages, the
lineages, and the clusters formed so far. -/
def branchStep (t : ℝ) (m : ℕ) (bs : List (Finset (Fin n))) (acc : Finset (Finset (Fin n)))
    (k : ℕ → List (Finset (Fin n)) → Finset (Finset (Fin n)) → ℝ) : ℝ :=
  ∑ j ∈ Icc 1 m, tavareProb m j t *
    ∫ h, k j (mergeAlong bs h (m - j)) (acc ∪ cladesAlong bs h (m - j)) ∂randomJoining m

/-- The law of the lineages leaving the top of the branch above a vertex of the species tree,
in continuation-passing form: `exitLaw T k` is the expectation of `k m bs acc`, where `m` is
the number of exiting lineages, `bs` the lineages and `acc` the clusters formed below. The two
daughter populations evolve independently, and their lineages enter the ancestral population
together. -/
def exitLaw : SpeciesTree n → (ℕ → List (Finset (Fin n)) → Finset (Finset (Fin n)) → ℝ) → ℝ
  | leaf i, k => k 1 [{i}] {{i}}
  | node l r t, k => exitLaw l fun ml bl al => exitLaw r fun mr br ar =>
      branchStep t (ml + mr) (bl ++ br) (al ∪ ar) k

/-- **The multispecies coalescent** (Pamilo & Nei 1988; Degnan & Salter 2005), one lineage
sampled per species: the probability that the gene tree, given by its set of clusters, lies in
the event `E`. Below the root, each branch population runs Kingman's coalescent for the
branch length (`branchStep`); in the root population all remaining lineages coalesce by
random joining. -/
def geneTreeProb (T : SpeciesTree n) (E : Finset (Finset (Fin n)) → Prop) [DecidablePred E] :
    ℝ :=
  match T with
  | leaf i => if E {{i}} then 1 else 0
  | node l r _ => exitLaw l fun ml bl al => exitLaw r fun mr br ar =>
      ∫ h, (if E (al ∪ ar ∪ cladesAlong (bl ++ br) h (ml + mr - 1)) then 1 else 0)
        ∂randomJoining (ml + mr)

/-- The branch length stored at the root of a species tree does not affect the gene tree. -/
theorem geneTreeProb_node_length (l r : SpeciesTree n) (t t' : ℝ)
    (E : Finset (Finset (Fin n)) → Prop) [DecidablePred E] :
    geneTreeProb (.node l r t) E = geneTreeProb (.node l r t') E :=
  rfl

/-- If a continuation takes the constant value `c` whenever at least one lineage exits, then
so does `exitLaw` (Tavaré's probabilities sum to one and random joining is a probability). -/
theorem exitLaw_eq_const (T : SpeciesTree n) (c : ℝ)
    (k : ℕ → List (Finset (Fin n)) → Finset (Finset (Fin n)) → ℝ)
    (hk : ∀ m bs acc, 1 ≤ m → k m bs acc = c) : exitLaw T k = c := by
  induction T generalizing k with
  | leaf i => exact hk 1 _ _ le_rfl
  | node l r t ihl ihr =>
    refine ihl _ fun ml bl al hml => ihr _ fun mr br ar hmr => ?_
    rw [branchStep, ← one_mul c, ← sum_tavareProb (show 1 ≤ ml + mr by omega) t,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_congr_ae (Filter.Eventually.of_forall fun h => hk j _ _ (mem_Icc.1 hj).1),
      integral_const, probReal_univ, one_smul]

/-- **The multispecies coalescent is a probability law**: for every species tree, the event
"any gene tree" has probability one (an identity for every real branch length). -/
theorem geneTreeProb_true (T : SpeciesTree n) : geneTreeProb T (fun _ => True) = 1 := by
  cases T with
  | leaf i => simp [geneTreeProb]
  | node l r t =>
    simp only [geneTreeProb, ite_true]
    exact exitLaw_eq_const l 1 _ fun ml bl al _ => exitLaw_eq_const r 1 _ fun mr br ar _ => by
      rw [integral_const, probReal_univ, one_smul]

/-! ### Evaluating random-joining expectations -/

/-- An expectation under random joining is the average over the `∏_{k=2}^m C(k, 2)` ranked
histories. -/
theorem integral_randomJoining (m : ℕ) (f : RankedHistory m → ℝ) :
    ∫ h, f h ∂randomJoining m = (∑ h, f h) / ∏ k ∈ Icc 2 m, ((k.choose 2 : ℕ) : ℝ) := by
  rw [integral_fintype (hf := .of_finite)]
  simp only [measureReal_def, randomJoining_singleton_eq_inv, smul_eq_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← Finset.sum_mul, div_eq_mul_inv, mul_comm]
  push_cast
  rfl

/-- `integral_randomJoining` for a rational-valued function, with a rational result (used to
evaluate random-joining probabilities by computation). -/
theorem integral_randomJoining_ratCast (m : ℕ) (q : RankedHistory m → ℚ) :
    ∫ h, (q h : ℝ) ∂randomJoining m =
      (((∑ h, q h) / ∏ k ∈ Icc 2 m, ((k.choose 2 : ℕ) : ℚ) : ℚ) : ℝ) := by
  rw [integral_randomJoining]
  push_cast
  rfl

/-- The probability of an event under random joining is the fraction of ranked histories in it. -/
theorem randomJoining_real (m : ℕ) (A : Set (RankedHistory m)) [DecidablePred (· ∈ A)] :
    (randomJoining m).real A = (#{h | h ∈ A} : ℝ) / ∏ k ∈ Icc 2 m, ((k.choose 2 : ℕ) : ℝ) := by
  rw [← integral_indicator_one (.of_discrete), integral_randomJoining]
  simp only [Set.indicator_apply, Pi.one_apply]
  rw [sum_boole]

private theorem integral_randomJoining_finsetSum {ι : Type*} (m : ℕ) (s : Finset ι)
    (f : ι → RankedHistory m → ℝ) :
    ∫ h, ∑ j ∈ s, f j h ∂randomJoining m = ∑ j ∈ s, ∫ h, f j h ∂randomJoining m :=
  integral_finsetSum _ fun _ _ => .of_finite

private theorem integral_randomJoining_add (m : ℕ) (f g : RankedHistory m → ℝ) :
    ∫ h, f h + g h ∂randomJoining m = ∫ h, f h ∂randomJoining m + ∫ h, g h ∂randomJoining m :=
  integral_add .of_finite .of_finite

private theorem sum_Icc_one_two (f : ℕ → ℝ) : ∑ j ∈ Icc 1 2, f j = f 1 + f 2 := by
  rw [show Icc 1 2 = {1, 2} by decide, sum_pair (by decide)]

private theorem sum_Icc_one_three (f : ℕ → ℝ) : ∑ j ∈ Icc 1 3, f j = f 1 + f 2 + f 3 := by
  rw [show Icc 1 3 = {1, 2, 3} by decide, sum_insert (by decide), sum_pair (by decide), add_assoc]

private theorem ite_one_zero_ratCast (p : Prop) [Decidable p] :
    (if p then (1 : ℝ) else 0) = ((if p then (1 : ℚ) else 0 : ℚ) : ℝ) := by
  split_ifs <;> simp

private theorem card_eq_le_of_forall {α β : Type*} [Fintype α] [DecidableEq β] (Φ : α → β)
    (M G : β) (P : β → Prop)
    (h : ∀ x, ¬ P (Φ x) → #{y | Φ y = Φ x} ≤ #{y | Φ y = M}) (hG : ¬ P G) :
    #{y | Φ y = G} ≤ #{y | Φ y = M} := by
  by_cases hx : ∃ x, Φ x = G
  · obtain ⟨x, rfl⟩ := hx
    exact h x hG
  · push Not at hx
    simp [hx]

private theorem integral_ite_le {m : ℕ} {β : Type*} [DecidableEq β] (Φ : RankedHistory m → β)
    (M G : β) (P : β → Prop)
    (h : ∀ x, ¬ P (Φ x) → #{y | Φ y = Φ x} ≤ #{y | Φ y = M}) (hG : ¬ P G) :
    ∫ x, (if Φ x = G then (1 : ℝ) else 0) ∂randomJoining m ≤
      ∫ x, (if Φ x = M then (1 : ℝ) else 0) ∂randomJoining m := by
  rw [integral_randomJoining, integral_randomJoining, sum_boole, sum_boole]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_eq_le_of_forall Φ M G P h hG)
    (prod_nonneg fun _ _ => by positivity)

private theorem integral_integral_ite_le {a b : ℕ} {β : Type*} [DecidableEq β]
    (Φ : RankedHistory a → RankedHistory b → β) (M G : β) (P : β → Prop)
    (h : ∀ x : RankedHistory a × RankedHistory b, ¬ P (Φ x.1 x.2) →
      #{y : RankedHistory a × RankedHistory b | Φ y.1 y.2 = Φ x.1 x.2} ≤
        #{y : RankedHistory a × RankedHistory b | Φ y.1 y.2 = M}) (hG : ¬ P G) :
    ∫ x, ∫ y, (if Φ x y = G then (1 : ℝ) else 0) ∂randomJoining b ∂randomJoining a ≤
      ∫ x, ∫ y, (if Φ x y = M then (1 : ℝ) else 0) ∂randomJoining b ∂randomJoining a := by
  simp only [integral_randomJoining, ← sum_div, div_div]
  rw [← Fintype.sum_prod_type' (f := fun x y => if Φ x y = G then (1 : ℝ) else 0),
    ← Fintype.sum_prod_type' (f := fun x y => if Φ x y = M then (1 : ℝ) else 0),
    sum_boole, sum_boole]
  have hc := card_eq_le_of_forall (fun x : RankedHistory a × RankedHistory b => Φ x.1 x.2)
    M G P h hG
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

/-! ### Tavaré's formula for two and three lineages -/

/-- Two lineages are still distinct after time `t` with probability `e^{-t}`. -/
theorem tavareProb_two_two (t : ℝ) : tavareProb 2 2 t = Real.exp (-t) := by
  simp [tavareProb, Nat.ascFactorial, Nat.descFactorial]
  ring_nf

/-- Two lineages have coalesced within time `t` with probability `1 - e^{-t}`. -/
theorem tavareProb_two_one (t : ℝ) : tavareProb 2 1 t = 1 - Real.exp (-t) := by
  simp [tavareProb, Finset.sum_Icc_succ_top, Nat.ascFactorial, Nat.descFactorial]
  ring_nf

/-- Three lineages are still distinct after time `t` with probability `e^{-3t}`. -/
theorem tavareProb_three_three (t : ℝ) : tavareProb 3 3 t = Real.exp (-(3 * t)) := by
  simp [tavareProb, Nat.ascFactorial, Nat.descFactorial]
  ring_nf

/-- Three lineages have two ancestors at time `t` with probability `(3/2)(e^{-t} - e^{-3t})`. -/
theorem tavareProb_three_two (t : ℝ) :
    tavareProb 3 2 t = 3 / 2 * (Real.exp (-t) - Real.exp (-(3 * t))) := by
  simp [tavareProb, Finset.sum_Icc_succ_top, Nat.ascFactorial, Nat.descFactorial]
  ring_nf

/-- Three lineages have one ancestor at time `t` with probability
`1 - (3/2) e^{-t} + (1/2) e^{-3t}`. -/
theorem tavareProb_three_one (t : ℝ) :
    tavareProb 3 1 t = 1 - 3 / 2 * Real.exp (-t) + 1 / 2 * Real.exp (-(3 * t)) := by
  simp [tavareProb, Finset.sum_Icc_succ_top, Nat.ascFactorial, Nat.descFactorial]
  ring_nf

private theorem tavareProb_nonneg_of_le_three {m j : ℕ} (hm : m ≤ 3) (hj : j ∈ Icc 1 m) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ tavareProb m j t := by
  have h1 : Real.exp (-t) ≤ 1 := by simpa using Real.exp_le_exp.mpr (show -t ≤ 0 by linarith)
  have h3 : Real.exp (-(3 * t)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  have h0 : 0 < Real.exp (-t) := Real.exp_pos _
  have h0' : 0 < Real.exp (-(3 * t)) := Real.exp_pos _
  have e3 : Real.exp (-(3 * t)) = Real.exp (-t) ^ 3 := by
    rw [← Real.exp_nat_mul]; ring_nf
  obtain ⟨hj1, hj2⟩ := mem_Icc.1 hj
  interval_cases m <;> interval_cases j
  · simp [tavareProb]
  · rw [tavareProb_two_one]; linarith
  · rw [tavareProb_two_two]; positivity
  · rw [tavareProb_three_one, e3]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1)) h0.le]
  · rw [tavareProb_three_two]; linarith
  · rw [tavareProb_three_three]; positivity

/-! ### Three species -/

/-- The three-species tree `((0, 1), 2)` with internal branch length `t`. -/
def triple (t : ℝ) : SpeciesTree 3 := .node (.node (.leaf 0) (.leaf 1) t) (.leaf 2) 0

/-- The gene tree on three genes with cherry `c` (a pair of genes), as a set of clusters. -/
def tripleTree (c : Finset (Fin 3)) : Finset (Finset (Fin 3)) := {{0}, {1}, {2}, c, univ}

/-- The species tree `((0, 1), 2)` has the clusters of the gene tree with cherry `{0, 1}`. -/
theorem clusters_triple (t : ℝ) : (triple t).clusters = tripleTree {0, 1} := by
  simp only [triple, clusters, taxa, tripleTree]
  decide

/-- **Three-species concordance** (Hudson 1983; Pamilo & Nei 1988): with one lineage per
species and internal branch length `t`, the gene tree matches the species tree with
probability `1 - (2/3) e^{-t}`. (An identity for every real `t`; branch lengths are `t ≥ 0`.) -/
theorem geneTreeProb_triple_matching (t : ℝ) :
    geneTreeProb (triple t) (· = tripleTree {0, 1}) = 1 - 2 / 3 * Real.exp (-t) := by
  simp only [geneTreeProb, triple, exitLaw, branchStep]
  rw [show Icc 1 (1 + 1) = {1, 2} by decide, sum_pair (by decide)]
  simp only [ite_one_zero_ratCast, integral_randomJoining_ratCast]
  have key : ∀ a b : ℚ, a = 1 → b = 1 / 3 →
      tavareProb 2 1 t * (a : ℝ) + tavareProb 2 2 t * (b : ℝ) = 1 - 2 / 3 * Real.exp (-t) := by
    rintro _ _ rfl rfl
    rw [tavareProb_two_one, tavareProb_two_two]
    push_cast
    ring
  exact key _ _ (by decide +kernel) (by decide +kernel)

/-- Each discordant three-species gene tree has probability `(1/3) e^{-t}`: cherry `{0, 2}`. -/
theorem geneTreeProb_triple_cherry_02 (t : ℝ) :
    geneTreeProb (triple t) (· = tripleTree {0, 2}) = 1 / 3 * Real.exp (-t) := by
  simp only [geneTreeProb, triple, exitLaw, branchStep]
  rw [show Icc 1 (1 + 1) = {1, 2} by decide, sum_pair (by decide)]
  simp only [ite_one_zero_ratCast, integral_randomJoining_ratCast]
  have key : ∀ a b : ℚ, a = 0 → b = 1 / 3 →
      tavareProb 2 1 t * (a : ℝ) + tavareProb 2 2 t * (b : ℝ) = 1 / 3 * Real.exp (-t) := by
    rintro _ _ rfl rfl
    rw [tavareProb_two_two]
    push_cast
    ring
  exact key _ _ (by decide +kernel) (by decide +kernel)

/-- Each discordant three-species gene tree has probability `(1/3) e^{-t}`: cherry `{1, 2}`. -/
theorem geneTreeProb_triple_cherry_12 (t : ℝ) :
    geneTreeProb (triple t) (· = tripleTree {1, 2}) = 1 / 3 * Real.exp (-t) := by
  simp only [geneTreeProb, triple, exitLaw, branchStep]
  rw [show Icc 1 (1 + 1) = {1, 2} by decide, sum_pair (by decide)]
  simp only [ite_one_zero_ratCast, integral_randomJoining_ratCast]
  have key : ∀ a b : ℚ, a = 0 → b = 1 / 3 →
      tavareProb 2 1 t * (a : ℝ) + tavareProb 2 2 t * (b : ℝ) = 1 / 3 * Real.exp (-t) := by
    rintro _ _ rfl rfl
    rw [tavareProb_two_two]
    push_cast
    ring
  exact key _ _ (by decide +kernel) (by decide +kernel)

/-- **No anomalous gene trees for three species** (Degnan & Rosenberg 2006): for a positive
internal branch, each discordant gene tree is strictly less probable than the matching one. -/
theorem triple_no_anomaly {t : ℝ} (ht : 0 < t) :
    geneTreeProb (triple t) (· = tripleTree {0, 2}) <
        geneTreeProb (triple t) (· = (triple t).clusters) ∧
      geneTreeProb (triple t) (· = tripleTree {1, 2}) <
        geneTreeProb (triple t) (· = (triple t).clusters) := by
  rw [clusters_triple, geneTreeProb_triple_matching, geneTreeProb_triple_cherry_02,
    geneTreeProb_triple_cherry_12]
  have : Real.exp (-t) < 1 := by simpa using Real.exp_lt_exp.mpr (show -t < 0 by linarith)
  constructor <;> linarith

/-- The three-species probabilities come from the Wright–Fisher model: in a population of `M`
gene copies, the lineages of species `0` and `1` have distinct parents in each of the
`⌊t M⌋` generations of the internal branch (`t ≥ 0` coalescent units) with probability
`noCoalProb M 2 ^ ⌊t M⌋`, which tends to `tavareProb 2 2 t = e^{-t}`, the weight of the case
in which three lineages reach the root population. -/
theorem tendsto_noCoalProb_pow_floor_two {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun M : ℕ => noCoalProb M 2 ^ ⌊t * M⌋₊) atTop (𝓝 (tavareProb 2 2 t)) := by
  rw [tavareProb_two_two]
  simpa using tendsto_noCoalProb_pow_floor 2 ht

/-! ### Four species: the anomaly zone -/

/-- The asymmetric (caterpillar) species tree `(((0, 1), 2), 3)`: `x` is the length of the
deeper internal branch (above the ancestor of `0, 1, 2`) and `y` that of the shallower one
(above the ancestor of `0, 1`), as in Degnan & Rosenberg (2006). -/
def caterpillar (x y : ℝ) : SpeciesTree 4 :=
  .node (.node (.node (.leaf 0) (.leaf 1) y) (.leaf 2) x) (.leaf 3) 0

/-- The symmetric (balanced) species tree `((0, 1), (2, 3))` with internal branch lengths `y₁`
(above the ancestor of `0, 1`) and `y₂` (above the ancestor of `2, 3`). -/
def balanced (y₁ y₂ : ℝ) : SpeciesTree 4 :=
  .node (.node (.leaf 0) (.leaf 1) y₁) (.node (.leaf 2) (.leaf 3) y₂) 0

/-- The asymmetric gene tree `(((a, b), c), d)` on four genes, as a set of clusters. -/
def caterpillarTree (a b c d : Fin 4) : Finset (Finset (Fin 4)) :=
  {{a}, {b}, {c}, {d}, {a, b}, {a, b, c}, univ}

/-- The symmetric gene tree `((a, b), (c, d))` on four genes, as a set of clusters. -/
def balancedTree (a b c d : Fin 4) : Finset (Finset (Fin 4)) :=
  {{a}, {b}, {c}, {d}, {a, b}, {c, d}, univ}

/-- The species tree `(((0, 1), 2), 3)` has the clusters of the gene tree `(((0, 1), 2), 3)`. -/
theorem clusters_caterpillar (x y : ℝ) : (caterpillar x y).clusters = caterpillarTree 0 1 2 3 := by
  simp only [caterpillar, clusters, taxa, caterpillarTree]
  decide

/-- Degnan & Rosenberg (2006), eq. (1): `f(x, y)`, the probability of the matching gene tree
`(((A, B), C), D)` on the caterpillar species tree. -/
def drF (x y : ℝ) : ℝ :=
  1 - 2 / 3 * Real.exp (-x) - 2 / 3 * Real.exp (-y) + 1 / 3 * Real.exp (-(x + y)) +
    1 / 18 * Real.exp (-(3 * x + y))

/-- Degnan & Rosenberg (2006), eq. (2): `g(x, y)`, the probability of the gene tree
`((A, C), (B, D))` (and of `((A, D), (B, C))`) on the caterpillar species tree. -/
def drG (x y : ℝ) : ℝ := 1 / 6 * Real.exp (-(x + y)) - 1 / 18 * Real.exp (-(3 * x + y))

/-- Degnan & Rosenberg (2006), eq. (3): `h(x, y)`, the probability of the gene tree
`((A, B), (C, D))` on the caterpillar species tree. -/
def drH (x y : ℝ) : ℝ :=
  1 / 3 * Real.exp (-x) - 1 / 6 * Real.exp (-(x + y)) - 1 / 18 * Real.exp (-(3 * x + y))

/-- The gene-tree probability on the caterpillar species tree, given the random-joining
probabilities `a, …, e` of the event in the five cases for the numbers of lineages leaving the
two internal branches (`1, 1`; `1, 2`; `2, 1`; `2, 2`; `2, 3` after the shallower and the deeper
branch). -/
private def catComb (x y : ℝ) (a b c d e : ℚ) : ℝ :=
  tavareProb 2 1 y * (tavareProb 2 1 x * (a : ℝ)) +
      tavareProb 2 1 y * (tavareProb 2 2 x * (b : ℝ)) +
    (tavareProb 2 2 y * (tavareProb 3 1 x * (c : ℝ)) +
      tavareProb 2 2 y * (tavareProb 3 2 x * (d : ℝ)) +
      tavareProb 2 2 y * (tavareProb 3 3 x * (e : ℝ)))

private theorem catComb_congr (x y : ℝ) {a b c d e : ℚ} (A B C D E : ℚ) (ha : a = A)
    (hb : b = B) (hc : c = C) (hd : d = D) (he : e = E) :
    catComb x y a b c d e = catComb x y A B C D E := by
  subst ha hb hc hd he
  rfl

/-- **The matching gene tree** on the caterpillar species tree has probability `f(x, y)`
(Degnan & Rosenberg 2006, eq. (1)). An identity for all real `x, y`. -/
theorem geneTreeProb_caterpillar_matching (x y : ℝ) :
    geneTreeProb (caterpillar x y) (· = caterpillarTree 0 1 2 3) = drF x y := by
  simp only [geneTreeProb, caterpillar, exitLaw, branchStep, Nat.reduceAdd, sum_Icc_one_two,
    sum_Icc_one_three, integral_randomJoining_finsetSum, integral_const_mul, mul_add,
    ite_one_zero_ratCast, integral_randomJoining_ratCast]
  refine (catComb_congr x y (1) (1/3) (1/3) (1/9) (1/18) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans ?_
  simp only [catComb, tavareProb_two_one, tavareProb_two_two, tavareProb_three_one,
    tavareProb_three_two, tavareProb_three_three, drF, neg_add, Real.exp_add]
  push_cast
  ring

/-- The symmetric gene tree `((A, C), (B, D))` on the caterpillar species tree has probability
`g(x, y)` (Degnan & Rosenberg 2006, eq. (2)). -/
theorem geneTreeProb_caterpillar_AC_BD (x y : ℝ) :
    geneTreeProb (caterpillar x y) (· = balancedTree 0 2 1 3) = drG x y := by
  simp only [geneTreeProb, caterpillar, exitLaw, branchStep, Nat.reduceAdd, sum_Icc_one_two,
    sum_Icc_one_three, integral_randomJoining_finsetSum, integral_const_mul, mul_add,
    ite_one_zero_ratCast, integral_randomJoining_ratCast]
  refine (catComb_congr x y (0) (0) (0) (1/9) (1/9) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans ?_
  simp only [catComb, tavareProb_two_one, tavareProb_two_two, tavareProb_three_one,
    tavareProb_three_two, tavareProb_three_three, drG, neg_add, Real.exp_add]
  push_cast
  ring

/-- The symmetric gene tree `((A, D), (B, C))` on the caterpillar species tree has probability
`g(x, y)`, the same as `((A, C), (B, D))` (Degnan & Rosenberg 2006). -/
theorem geneTreeProb_caterpillar_AD_BC (x y : ℝ) :
    geneTreeProb (caterpillar x y) (· = balancedTree 0 3 1 2) = drG x y := by
  simp only [geneTreeProb, caterpillar, exitLaw, branchStep, Nat.reduceAdd, sum_Icc_one_two,
    sum_Icc_one_three, integral_randomJoining_finsetSum, integral_const_mul, mul_add,
    ite_one_zero_ratCast, integral_randomJoining_ratCast]
  refine (catComb_congr x y (0) (0) (0) (1/9) (1/9) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans ?_
  simp only [catComb, tavareProb_two_one, tavareProb_two_two, tavareProb_three_one,
    tavareProb_three_two, tavareProb_three_three, drG, neg_add, Real.exp_add]
  push_cast
  ring

/-- The symmetric gene tree `((A, B), (C, D))` on the caterpillar species tree has probability
`h(x, y)` (Degnan & Rosenberg 2006, eq. (3)). -/
theorem geneTreeProb_caterpillar_AB_CD (x y : ℝ) :
    geneTreeProb (caterpillar x y) (· = balancedTree 0 1 2 3) = drH x y := by
  simp only [geneTreeProb, caterpillar, exitLaw, branchStep, Nat.reduceAdd, sum_Icc_one_two,
    sum_Icc_one_three, integral_randomJoining_finsetSum, integral_const_mul, mul_add,
    ite_one_zero_ratCast, integral_randomJoining_ratCast]
  refine (catComb_congr x y (0) (1/3) (0) (1/9) (1/9) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans ?_
  simp only [catComb, tavareProb_two_one, tavareProb_two_two, tavareProb_three_one,
    tavareProb_three_two, tavareProb_three_three, drH, neg_add, Real.exp_add]
  push_cast
  ring

/-- Degnan & Rosenberg (2006), eq. (4): the boundary `a(x)` of the four-species anomaly zone,
for a deeper internal branch of length `x > 0` (at `x = 0` the denominator vanishes and Lean's
`a / 0 = 0` gives the junk value `log (2/3 - 0)`; `a(x) → ∞` as `x → 0⁺`). -/
def anomalyA (x : ℝ) : ℝ :=
  Real.log (2 / 3 + (3 * Real.exp (2 * x) - 2) / (18 * (Real.exp (3 * x) - Real.exp (2 * x))))

/-- Degnan & Rosenberg (2006), eq. (5): the boundary `b(x)` below which the caterpillar species
tree has three anomalous gene trees (defined for `x ≥ 0`). -/
def anomalyB (x : ℝ) : ℝ :=
  Real.log (2 / 3 + (5 * Real.exp (2 * x) - 2) / (6 * (3 * Real.exp (3 * x) -
    2 * Real.exp (2 * x))))

/-- For a positive shallower branch, the symmetric gene tree `((A, B), (C, D))` is strictly more
probable than `((A, C), (B, D))`: `g(x, y) < h(x, y)` (Degnan & Rosenberg 2006). -/
theorem drG_lt_drH (x : ℝ) {y : ℝ} (hy : 0 < y) : drG x y < drH x y := by
  unfold drG drH
  have h1 : Real.exp (-(x + y)) = Real.exp (-x) * Real.exp (-y) := by
    rw [neg_add, Real.exp_add]
  have h2 : Real.exp (-y) < 1 := by simpa using Real.exp_lt_exp.mpr (show -y < 0 by linarith)
  have h3 := Real.exp_pos (-x)
  rw [h1]
  nlinarith

/-- **The boundary `a(x)` of the anomaly zone** (Degnan & Rosenberg 2006): for a deeper
internal branch `x > 0`, the symmetric gene tree `((A, B), (C, D))` is more probable than the
matching gene tree, `f(x, y) < h(x, y)`, if and only if `y < a(x)`. -/
theorem drF_lt_drH_iff {x : ℝ} (hx : 0 < x) (y : ℝ) : drF x y < drH x y ↔ y < anomalyA x := by
  have hx' : 0 ≤ x := hx.le
  have hE : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx'
  set E := Real.exp x with hEdef
  have e1 : Real.exp (-x) = E⁻¹ := Real.exp_neg x
  have e2 : Real.exp (-(x + y)) = E⁻¹ * Real.exp (-y) := by rw [neg_add, Real.exp_add, e1]
  have e5 : Real.exp (3 * x) = E ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have e4 : Real.exp (2 * x) = E ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp (-(3 * x + y)) = (E ^ 3)⁻¹ * Real.exp (-y) := by
    rw [neg_add, Real.exp_add, Real.exp_neg, e5]
  have ey : Real.exp y = (Real.exp (-y))⁻¹ := by rw [Real.exp_neg, inv_inv]
  have hS : 0 < Real.exp (-y) := Real.exp_pos _
  set S := Real.exp (-y)
  have hE0 : 0 < E := by linarith
  have hE1 : 1 < E := by simpa [hEdef] using Real.exp_lt_exp.mpr hx
  have hEE : 0 < E ^ 3 - E ^ 2 := by
    rw [show E ^ 3 - E ^ 2 = E ^ 2 * (E - 1) by ring]
    exact mul_pos (by positivity) (by linarith)
  have hN : 0 < 12 * E ^ 3 - 9 * E ^ 2 - 2 := by nlinarith
  have hA : 2 / 3 + (3 * E ^ 2 - 2) / (18 * (E ^ 3 - E ^ 2)) =
      (12 * E ^ 3 - 9 * E ^ 2 - 2) / (18 * (E ^ 3 - E ^ 2)) := by
    field_simp
    ring
  have key : drF x y - drH x y =
      (18 * (E ^ 3 - E ^ 2) - S * (12 * E ^ 3 - 9 * E ^ 2 - 2)) / (18 * E ^ 3) := by
    unfold drF drH
    rw [e1, e2, e3]
    field_simp
    ring
  unfold anomalyA
  rw [e4, e5, hA, Real.lt_log_iff_exp_lt (by positivity), ey, ← sub_neg, key,
    div_lt_iff₀ (by positivity), zero_mul, inv_eq_one_div, div_lt_div_iff₀ hS (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Degnan & Rosenberg (2006): for `x ≥ 0`, the gene tree `((A, C), (B, D))` (equivalently
`((A, D), (B, C))`) is more probable than the matching gene tree, `f(x, y) < g(x, y)`, if and
only if `y < b(x)`. -/
theorem drF_lt_drG_iff {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : drF x y < drG x y ↔ y < anomalyB x := by
  have hx' : 0 ≤ x := hx
  have hE : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx'
  set E := Real.exp x with hEdef
  have e1 : Real.exp (-x) = E⁻¹ := Real.exp_neg x
  have e2 : Real.exp (-(x + y)) = E⁻¹ * Real.exp (-y) := by rw [neg_add, Real.exp_add, e1]
  have e5 : Real.exp (3 * x) = E ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have e4 : Real.exp (2 * x) = E ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp (-(3 * x + y)) = (E ^ 3)⁻¹ * Real.exp (-y) := by
    rw [neg_add, Real.exp_add, Real.exp_neg, e5]
  have ey : Real.exp y = (Real.exp (-y))⁻¹ := by rw [Real.exp_neg, inv_inv]
  have hS : 0 < Real.exp (-y) := Real.exp_pos _
  set S := Real.exp (-y)
  have hE0 : 0 < E := by linarith
  have hD : 0 < 18 * E ^ 3 - 12 * E ^ 2 := by nlinarith
  have hD' : 0 < 6 * (3 * E ^ 3 - 2 * E ^ 2) := by nlinarith
  have hN : 0 < 12 * E ^ 3 - 3 * E ^ 2 - 2 := by nlinarith
  have hB : 2 / 3 + (5 * E ^ 2 - 2) / (6 * (3 * E ^ 3 - 2 * E ^ 2)) =
      (12 * E ^ 3 - 3 * E ^ 2 - 2) / (18 * E ^ 3 - 12 * E ^ 2) := by
    rw [div_add_div _ _ (by norm_num) hD'.ne', div_eq_div_iff (by positivity) hD.ne']
    ring
  have key : drF x y - drG x y =
      (18 * E ^ 3 - 12 * E ^ 2 - S * (12 * E ^ 3 - 3 * E ^ 2 - 2)) / (18 * E ^ 3) := by
    unfold drF drG
    rw [e1, e2, e3]
    field_simp
    ring
  unfold anomalyB
  rw [e4, e5, hB, Real.lt_log_iff_exp_lt (by positivity), ey, ← sub_neg, key,
    div_lt_iff₀ (by positivity), zero_mul, inv_eq_one_div, div_lt_div_iff₀ hS (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- `b(0) = log (7/6)` (Degnan & Rosenberg 2006): if `y ≥ log (7/6)`, then `y ≥ b(x)` for every
`x ≥ 0` (`anomalyB_le_anomalyB_zero`). -/
theorem anomalyB_zero : anomalyB 0 = Real.log (7 / 6) := by
  unfold anomalyB
  norm_num

/-- `b` is maximal at `0`: `b(x) ≤ log (7/6)` for `x ≥ 0`, so for `y ≥ log (7/6)` at most one
gene tree is anomalous. -/
theorem anomalyB_le_anomalyB_zero {x : ℝ} (hx : 0 ≤ x) : anomalyB x ≤ anomalyB 0 := by
  have hE : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
  have e5 : Real.exp (3 * x) = Real.exp x ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have e4 : Real.exp (2 * x) = Real.exp x ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  set E := Real.exp x
  have hD : 0 < 6 * (3 * E ^ 3 - 2 * E ^ 2) := by nlinarith
  have hN : 0 < 5 * E ^ 2 - 2 := by nlinarith
  rw [anomalyB_zero]
  unfold anomalyB
  rw [e4, e5]
  refine Real.log_le_log (by positivity) ?_
  suffices (5 * E ^ 2 - 2) / (6 * (3 * E ^ 3 - 2 * E ^ 2)) ≤ 1 / 2 by linarith
  rw [div_le_iff₀ hD]
  nlinarith [mul_nonneg (sub_nonneg.2 hE) (sub_nonneg.2 hE)]

/-- `a(x) → ∞` as `x → 0⁺` (Degnan & Rosenberg 2006): very short deep branches produce an
anomalous gene tree however long the shallower branch is. -/
theorem tendsto_anomalyA : Tendsto anomalyA (𝓝[>] 0) atTop := by
  have hnum : Tendsto (fun x : ℝ => 3 * Real.exp (2 * x) - 2) (𝓝[>] 0) (𝓝 1) := by
    have : Continuous fun x : ℝ => 3 * Real.exp (2 * x) - 2 := by fun_prop
    have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    norm_num at h
    exact h
  have hden : Tendsto (fun x : ℝ => 18 * (Real.exp (3 * x) - Real.exp (2 * x))) (𝓝[>] 0)
      (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Continuous fun x : ℝ => 18 * (Real.exp (3 * x) - Real.exp (2 * x)) := by fun_prop
      have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      norm_num at h
      exact h
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      have : Real.exp (2 * x) < Real.exp (3 * x) := Real.exp_lt_exp.mpr (by linarith)
      simp only [Set.mem_Ioi]
      linarith
  have hfrac := hnum.pos_mul_atTop one_pos (tendsto_inv_nhdsGT_zero.comp hden)
  have harg := tendsto_atTop_add_const_left (𝓝[>] (0 : ℝ)) (2 / 3) hfrac
  refine (Real.tendsto_log_atTop.comp harg).congr fun x => ?_
  simp [anomalyA, div_eq_mul_inv]

/-- **Anomalous gene tree on four species** (Degnan & Rosenberg 2006): on the caterpillar
species tree with deeper branch `x > 0` and shallower branch `y`, the symmetric gene tree
`((A, B), (C, D))` is more probable than the gene tree matching the species tree if and only
if `y < a(x)`. With `caterpillar_le_matching` this gives `caterpillar_exists_anomalous_iff`. -/
theorem caterpillar_anomalous_iff {x : ℝ} (hx : 0 < x) (y : ℝ) :
    geneTreeProb (caterpillar x y) (· = (caterpillar x y).clusters) <
        geneTreeProb (caterpillar x y) (· = balancedTree 0 1 2 3) ↔ y < anomalyA x := by
  rw [clusters_caterpillar, geneTreeProb_caterpillar_matching, geneTreeProb_caterpillar_AB_CD,
    drF_lt_drH_iff hx]

/-- On the caterpillar species tree with `x ≥ 0`, the gene trees `((A, C), (B, D))` and
`((A, D), (B, C))` are more probable than the matching gene tree if and only if `y < b(x)`. -/
theorem caterpillar_anomalous_AC_BD_iff {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    geneTreeProb (caterpillar x y) (· = (caterpillar x y).clusters) <
        geneTreeProb (caterpillar x y) (· = balancedTree 0 2 1 3) ↔ y < anomalyB x := by
  rw [clusters_caterpillar, geneTreeProb_caterpillar_matching, geneTreeProb_caterpillar_AC_BD,
    drF_lt_drG_iff hx]

/-- `G` is one of the three balanced (symmetric) gene trees on four genes. -/
def IsBalancedGeneTree (G : Finset (Finset (Fin 4))) : Prop :=
  G = balancedTree 0 1 2 3 ∨ G = balancedTree 0 2 1 3 ∨ G = balancedTree 0 3 1 2

instance : DecidablePred IsBalancedGeneTree := fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- On the caterpillar species tree with nonnegative branch lengths, no asymmetric gene tree is
more probable than the matching one (Degnan & Rosenberg 2006): only the three balanced gene
trees can be anomalous. -/
theorem caterpillar_le_matching {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (G : Finset (Finset (Fin 4)))
    (hG : ¬ IsBalancedGeneTree G) :
    geneTreeProb (caterpillar x y) (· = G) ≤
      geneTreeProb (caterpillar x y) (· = caterpillarTree 0 1 2 3) := by
  simp only [geneTreeProb, caterpillar, exitLaw, branchStep, Nat.reduceAdd]
  refine sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_
    (tavareProb_nonneg_of_le_three (by norm_num) hj hy)
  refine integral_mono .of_finite .of_finite fun h => ?_
  refine sum_le_sum fun j' hj' => mul_le_mul_of_nonneg_left ?_
    (tavareProb_nonneg_of_le_three (by simp at hj; omega) hj' hx)
  refine integral_integral_ite_le _ _ _ IsBalancedGeneTree ?_ hG
  simp only [mem_Icc] at hj hj'
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · rcases (show j' = 1 ∨ j' = 2 by omega) with rfl | rfl <;> revert h <;> decide +kernel
  · rcases (show j' = 1 ∨ j' = 2 ∨ j' = 3 by omega) with rfl | rfl | rfl <;> revert h <;>
      decide +kernel

/-- `g(x, y) ≤ h(x, y)` for a nonnegative shallower branch (equality at `y = 0`). -/
theorem drG_le_drH (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : drG x y ≤ drH x y := by
  unfold drG drH
  have h1 : Real.exp (-(x + y)) = Real.exp (-x) * Real.exp (-y) := by
    rw [neg_add, Real.exp_add]
  have h2 : Real.exp (-y) ≤ 1 := by simpa using Real.exp_le_exp.mpr (show -y ≤ 0 by linarith)
  have h3 := Real.exp_pos (-x)
  rw [h1]
  nlinarith

/-- **The four-species anomaly zone** (Degnan & Rosenberg 2006, Definition 1 and Figure 2): the
caterpillar species tree with deeper branch `x > 0` and shallower branch `y ≥ 0` has an
anomalous gene tree, one strictly more probable than the gene tree matching the species
tree, if and only if `y < a(x)`. -/
theorem caterpillar_exists_anomalous_iff {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    (∃ G, geneTreeProb (caterpillar x y) (· = (caterpillar x y).clusters) <
        geneTreeProb (caterpillar x y) (· = G)) ↔ y < anomalyA x := by
  rw [← caterpillar_anomalous_iff hx y]
  refine ⟨fun ⟨G, hG⟩ => ?_, fun h => ⟨_, h⟩⟩
  rw [clusters_caterpillar] at hG ⊢
  by_cases hb : IsBalancedGeneTree G
  · rcases hb with rfl | rfl | rfl
    · exact hG
    · rw [geneTreeProb_caterpillar_AB_CD]
      rw [geneTreeProb_caterpillar_AC_BD] at hG
      exact hG.trans_le (drG_le_drH x hy)
    · rw [geneTreeProb_caterpillar_AB_CD]
      rw [geneTreeProb_caterpillar_AD_BC] at hG
      exact hG.trans_le (drG_le_drH x hy)
  · exact absurd (caterpillar_le_matching hx.le hy G hb) (not_le.2 hG)

/-- **No anomalous gene trees on the balanced four-species tree** (Degnan & Rosenberg 2006):
for nonnegative branch lengths, no gene tree is more probable than the one matching the
species tree `((0, 1), (2, 3))`. Given the numbers of lineages entering the root population,
the matching tree is already the most probable outcome of random joining. -/
theorem balanced_no_anomaly {y₁ y₂ : ℝ} (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂)
    (G : Finset (Finset (Fin 4))) :
    geneTreeProb (balanced y₁ y₂) (· = G) ≤
      geneTreeProb (balanced y₁ y₂) (· = balancedTree 0 1 2 3) := by
  simp only [geneTreeProb, balanced, exitLaw, branchStep, Nat.reduceAdd]
  refine sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_
    (tavareProb_nonneg_of_le_three (by norm_num) hj hy₁)
  refine integral_mono .of_finite .of_finite fun h => ?_
  refine sum_le_sum fun j' hj' => mul_le_mul_of_nonneg_left ?_
    (tavareProb_nonneg_of_le_three (by norm_num) hj' hy₂)
  refine integral_mono .of_finite .of_finite fun h' => ?_
  refine integral_ite_le _ _ _ (fun _ => False) ?_ not_false
  simp only [not_false_eq_true, forall_const]
  rcases (show j = 1 ∨ j = 2 by simp at hj; omega) with rfl | rfl <;>
  rcases (show j' = 1 ∨ j' = 2 by simp at hj'; omega) with rfl | rfl <;>
  revert h h' <;> decide +kernel

/-! ### Unrooted quartets -/

/-- A rooted gene tree on four genes `G` (a set of clusters) **displays the quartet split**
`ab | cd`, where `{c, d}` is the complement of `{a, b}`: forgetting the root, the internal edge
separates `{a, b}` from `{c, d}`; equivalently `{a, b}` or `{c, d}` is a cluster. -/
def DisplaysSplit (a b : Fin 4) (G : Finset (Finset (Fin 4))) : Prop :=
  {a, b} ∈ G ∨ univ \ {a, b} ∈ G

instance (a b : Fin 4) : DecidablePred (DisplaysSplit a b) := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- **No anomalous unrooted quartets, caterpillar species tree** (Allman, Degnan & Rhodes 2011):
the unrooted gene quartet matches the species quartet `01 | 23` with probability
`1 - (2/3) e^{-y}`, where `y` is the length of the internal edge of the unrooted species
quartet (the shallower internal branch). -/
theorem geneTreeProb_caterpillar_split_01 (x y : ℝ) :
    geneTreeProb (caterpillar x y) (DisplaysSplit 0 1) = 1 - 2 / 3 * Real.exp (-y) := by
  simp only [geneTreeProb, caterpillar, exitLaw, branchStep, Nat.reduceAdd, sum_Icc_one_two,
    sum_Icc_one_three, integral_randomJoining_finsetSum, integral_const_mul, mul_add,
    ite_one_zero_ratCast, integral_randomJoining_ratCast]
  refine (catComb_congr x y 1 1 (1 / 3) (1 / 3) (1 / 3) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans ?_
  simp only [catComb, tavareProb_two_one, tavareProb_two_two, tavareProb_three_one,
    tavareProb_three_two, tavareProb_three_three]
  push_cast
  ring

/-- On the caterpillar species tree the discordant unrooted gene quartet `02 | 13` has
probability `(1/3) e^{-y}`. -/
theorem geneTreeProb_caterpillar_split_02 (x y : ℝ) :
    geneTreeProb (caterpillar x y) (DisplaysSplit 0 2) = 1 / 3 * Real.exp (-y) := by
  simp only [geneTreeProb, caterpillar, exitLaw, branchStep, Nat.reduceAdd, sum_Icc_one_two,
    sum_Icc_one_three, integral_randomJoining_finsetSum, integral_const_mul, mul_add,
    ite_one_zero_ratCast, integral_randomJoining_ratCast]
  refine (catComb_congr x y 0 0 (1 / 3) (1 / 3) (1 / 3) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans ?_
  simp only [catComb, tavareProb_two_one, tavareProb_two_two, tavareProb_three_one,
    tavareProb_three_two, tavareProb_three_three]
  push_cast
  ring

/-- On the caterpillar species tree the discordant unrooted gene quartet `03 | 12` has
probability `(1/3) e^{-y}`. -/
theorem geneTreeProb_caterpillar_split_03 (x y : ℝ) :
    geneTreeProb (caterpillar x y) (DisplaysSplit 0 3) = 1 / 3 * Real.exp (-y) := by
  simp only [geneTreeProb, caterpillar, exitLaw, branchStep, Nat.reduceAdd, sum_Icc_one_two,
    sum_Icc_one_three, integral_randomJoining_finsetSum, integral_const_mul, mul_add,
    ite_one_zero_ratCast, integral_randomJoining_ratCast]
  refine (catComb_congr x y 0 0 (1 / 3) (1 / 3) (1 / 3) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans ?_
  simp only [catComb, tavareProb_two_one, tavareProb_two_two, tavareProb_three_one,
    tavareProb_three_two, tavareProb_three_three]
  push_cast
  ring

/-- The gene-tree probability on the balanced species tree, given the random-joining
probabilities `a, b, c, d` of the event in the four cases for the numbers of lineages leaving
the two internal branches (`1, 1`; `1, 2`; `2, 1`; `2, 2`). -/
private def balComb (y₁ y₂ : ℝ) (a b c d : ℚ) : ℝ :=
  tavareProb 2 1 y₁ * (tavareProb 2 1 y₂ * (a : ℝ)) +
      tavareProb 2 1 y₁ * (tavareProb 2 2 y₂ * (b : ℝ)) +
    (tavareProb 2 2 y₁ * (tavareProb 2 1 y₂ * (c : ℝ)) +
      tavareProb 2 2 y₁ * (tavareProb 2 2 y₂ * (d : ℝ)))

private theorem balComb_congr (y₁ y₂ : ℝ) {a b c d : ℚ} (A B C D : ℚ) (ha : a = A)
    (hb : b = B) (hc : c = C) (hd : d = D) :
    balComb y₁ y₂ a b c d = balComb y₁ y₂ A B C D := by
  subst ha hb hc hd
  rfl

/-- **No anomalous unrooted quartets, balanced species tree** (Allman, Degnan & Rhodes 2011):
on `((0, 1), (2, 3))` the unrooted gene quartet matches `01 | 23` with probability
`1 - (2/3) e^{-(y₁ + y₂)}`, where `y₁ + y₂` is the internal edge of the unrooted species
quartet. -/
theorem geneTreeProb_balanced_split_01 (y₁ y₂ : ℝ) :
    geneTreeProb (balanced y₁ y₂) (DisplaysSplit 0 1) = 1 - 2 / 3 * Real.exp (-(y₁ + y₂)) := by
  simp only [geneTreeProb, balanced, exitLaw, branchStep, Nat.reduceAdd, sum_Icc_one_two,
    integral_randomJoining_add, integral_const_mul, mul_add, ite_one_zero_ratCast,
    integral_randomJoining_ratCast]
  refine (balComb_congr y₁ y₂ 1 1 1 (1 / 3) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).trans ?_
  simp only [balComb, tavareProb_two_one, tavareProb_two_two, neg_add, Real.exp_add]
  push_cast
  ring

/-- On the balanced species tree the discordant unrooted gene quartet `02 | 13` has
probability `(1/3) e^{-(y₁ + y₂)}`. -/
theorem geneTreeProb_balanced_split_02 (y₁ y₂ : ℝ) :
    geneTreeProb (balanced y₁ y₂) (DisplaysSplit 0 2) = 1 / 3 * Real.exp (-(y₁ + y₂)) := by
  simp only [geneTreeProb, balanced, exitLaw, branchStep, Nat.reduceAdd, sum_Icc_one_two,
    integral_randomJoining_add, integral_const_mul, mul_add, ite_one_zero_ratCast,
    integral_randomJoining_ratCast]
  refine (balComb_congr y₁ y₂ 0 0 0 (1 / 3) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).trans ?_
  simp only [balComb, tavareProb_two_two, neg_add, Real.exp_add]
  push_cast
  ring

/-- On the balanced species tree the discordant unrooted gene quartet `03 | 12` has
probability `(1/3) e^{-(y₁ + y₂)}`. -/
theorem geneTreeProb_balanced_split_03 (y₁ y₂ : ℝ) :
    geneTreeProb (balanced y₁ y₂) (DisplaysSplit 0 3) = 1 / 3 * Real.exp (-(y₁ + y₂)) := by
  simp only [geneTreeProb, balanced, exitLaw, branchStep, Nat.reduceAdd, sum_Icc_one_two,
    integral_randomJoining_add, integral_const_mul, mul_add, ite_one_zero_ratCast,
    integral_randomJoining_ratCast]
  refine (balComb_congr y₁ y₂ 0 0 0 (1 / 3) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).trans ?_
  simp only [balComb, tavareProb_two_two, neg_add, Real.exp_add]
  push_cast
  ring

/-- **The species quartet maximizes quartet support** (Allman, Degnan & Rhodes 2011; Mirarab
et al. 2014): for a positive internal edge, the unrooted gene quartet matching the species
quartet is strictly the most probable of the three, on both four-species shapes. Since the
expected quartet support of a candidate four-species tree (one quartet) is the probability
of its quartet, the species tree maximizes it. -/
theorem split_01_most_probable {x y y₁ y₂ : ℝ} (hy : 0 < y) (hy₁₂ : 0 < y₁ + y₂) :
    geneTreeProb (caterpillar x y) (DisplaysSplit 0 2) <
        geneTreeProb (caterpillar x y) (DisplaysSplit 0 1) ∧
      geneTreeProb (caterpillar x y) (DisplaysSplit 0 3) <
        geneTreeProb (caterpillar x y) (DisplaysSplit 0 1) ∧
      geneTreeProb (balanced y₁ y₂) (DisplaysSplit 0 2) <
        geneTreeProb (balanced y₁ y₂) (DisplaysSplit 0 1) ∧
      geneTreeProb (balanced y₁ y₂) (DisplaysSplit 0 3) <
        geneTreeProb (balanced y₁ y₂) (DisplaysSplit 0 1) := by
  rw [geneTreeProb_caterpillar_split_01, geneTreeProb_caterpillar_split_02,
    geneTreeProb_caterpillar_split_03, geneTreeProb_balanced_split_01,
    geneTreeProb_balanced_split_02, geneTreeProb_balanced_split_03]
  have h1 : Real.exp (-y) < 1 := by simpa using Real.exp_lt_exp.mpr (show -y < 0 by linarith)
  have h2 : Real.exp (-(y₁ + y₂)) < 1 := by
    simpa using Real.exp_lt_exp.mpr (show -(y₁ + y₂) < 0 by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-! ### Clade probabilities under random joining -/

/-- The set `S` of sampled genes is a **clade** of the ranked history `h`: it is a block of one
of the ancestral partitions of `h`, i.e. the set of descendants of some lineage. -/
def IsClade {m : ℕ} (h : RankedHistory m) (S : Finset (Fin m)) : Prop :=
  ∃ P ∈ partitionsOf h, S ∈ P

instance {m : ℕ} (h : RankedHistory m) (S : Finset (Fin m)) : Decidable (IsClade h S) :=
  inferInstanceAs (Decidable (∃ P ∈ partitionsOf h, S ∈ P))

/-- **Clade probability** (Rosenberg 2003), checked for samples of at most five
genes: under random joining, a fixed set of `k` among `m` genes, `1 ≤ k < m`, is a clade with
probability `2m / (k (k + 1) C(m, k))`. The statement for all `m` is
`MultispeciesCoalescentWanted.randomJoining_isClade`. -/
theorem randomJoining_isClade_of_le_five {m : ℕ} (hm : m ≤ 5) (S : Finset (Fin m))
    (hS : 1 ≤ S.card) (hSm : S.card < m) :
    (randomJoining m).real {h | IsClade h S} =
      2 * m / (S.card * (S.card + 1) * (m.choose S.card : ℝ)) := by
  have hcount : #{h | IsClade h S} * (S.card * (S.card + 1) * m.choose S.card) =
      2 * m * ∏ k ∈ Icc 2 m, k.choose 2 := by
    revert S
    interval_cases m <;> decide +kernel
  rw [randomJoining_real]
  simp only [Set.mem_ofPred_eq]
  have hN : (0 : ℝ) < ∏ k ∈ Icc 2 m, ((k.choose 2 : ℕ) : ℝ) :=
    prod_pos fun k hk => by exact_mod_cast Nat.choose_pos (mem_Icc.1 hk).1
  have hC : (0 : ℝ) < S.card * (S.card + 1) * (m.choose S.card : ℝ) := by
    have : 0 < m.choose S.card := Nat.choose_pos hSm.le
    positivity
  rw [div_eq_div_iff hN.ne' hC.ne']
  have := congrArg (fun n : ℕ => (n : ℝ)) hcount
  push_cast at this
  linarith

end MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescent
