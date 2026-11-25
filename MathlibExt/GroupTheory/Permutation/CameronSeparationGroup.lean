/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.Permutation.HighlyHomogeneous
public import MathlibExt.GroupTheory.Permutation.PointwiseTopology
public import MathlibExt.GroupTheory.Permutation.Separation
import MathlibExt.GroupTheory.Permutation.CameronCircularOrderGroup
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Constructions

open MetaMathlibExt.CameronCircularOrderGroupWanted

section
namespace MetaMathlibExt.CameronSeparationHelpers

/-- The separation automorphism group is closed in the pointwise topology. This is the
closedness proof of `circularOrderAutSubgroup` with three points replaced by four. -/
private theorem sep_isClosed_separationAutSubgroup {α : Type*} [CircularOrder α] :
    @IsClosed (Equiv.Perm α) (Equiv.Perm.pointwiseTopology (α := α))
      ↑(MetaMathlibExt.separationAutSubgroup α) := by
  let : TopologicalSpace (Equiv.Perm α) := Equiv.Perm.pointwiseTopology (α := α)
  let : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  have : DiscreteTopology (Fin 4 → α) := Pi.discreteTopology
  have hcoe : Continuous (fun σ : Equiv.Perm α => (σ : α → α)) := continuous_induced_dom
  have heval : ∀ a : α, Continuous (fun σ : Equiv.Perm α => σ a) :=
    fun a => (continuous_apply a).comp hcoe
  have hfib : ∀ a b c d : α,
      IsClosed {σ : Equiv.Perm α | (MetaMathlibExt.circularSeparates a b c d ↔
        MetaMathlibExt.circularSeparates (σ a) (σ b) (σ c) (σ d))} := by
    intro a b c d
    let f : Equiv.Perm α → (Fin 4 → α) := fun σ => ![σ a, σ b, σ c, σ d]
    have hf : Continuous f := by
      rw [continuous_pi_iff]
      intro i
      fin_cases i
      · simpa [f] using heval a
      · simpa [f] using heval b
      · simpa [f] using heval c
      · simpa [f] using heval d
    have heq : {σ : Equiv.Perm α | (MetaMathlibExt.circularSeparates a b c d ↔
        MetaMathlibExt.circularSeparates (σ a) (σ b) (σ c) (σ d))}
        = f ⁻¹' {p : Fin 4 → α | (MetaMathlibExt.circularSeparates a b c d ↔
          MetaMathlibExt.circularSeparates (p 0) (p 1) (p 2) (p 3))} := by
      ext σ
      simp [f]
    rw [heq]
    exact IsClosed.preimage hf (isClosed_discrete _)
  have hset : (↑(MetaMathlibExt.separationAutSubgroup α) : Set (Equiv.Perm α))
      = ⋂ a, ⋂ b, ⋂ c, ⋂ d, {σ : Equiv.Perm α |
        (MetaMathlibExt.circularSeparates a b c d ↔
          MetaMathlibExt.circularSeparates (σ a) (σ b) (σ c) (σ d))} := by
    ext σ
    simp [MetaMathlibExt.mem_separationAutSubgroup, Set.mem_iInter]
  rw [hset]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun c =>
    isClosed_iInter fun d => hfib a b c d

/-- Every circular-order automorphism preserves the separation relation, since
`circularSeparates` is a Boolean combination of `sbtw` facts. -/
private theorem sep_circularOrder_le_separation (α : Type*) [CircularOrder α] :
    MetaMathlibExt.circularOrderAutSubgroup α ≤
      MetaMathlibExt.separationAutSubgroup α := by
  intro σ hσ
  have hbtw : ∀ x y z : α, btw x y z ↔ btw (σ x) (σ y) (σ z) :=
    (MetaMathlibExt.mem_circularOrderAutSubgroup σ).mp hσ
  have hsbtw : ∀ x y z : α, sbtw x y z ↔ sbtw (σ x) (σ y) (σ z) := by
    intro x y z
    rw [sbtw_iff_btw_not_btw, sbtw_iff_btw_not_btw]
    exact and_congr (hbtw x y z) (not_congr (hbtw z y x))
  rw [MetaMathlibExt.mem_separationAutSubgroup]
  intro a b c d
  unfold MetaMathlibExt.circularSeparates
  rw [hsbtw a c b, hsbtw b d a, hsbtw a d b, hsbtw b c a]

/-- High homogeneity passes to larger permutation subgroups. -/
private theorem sep_highlyHomogeneous_mono {α : Type*} [DecidableEq α]
    {G G' : Subgroup (Equiv.Perm α)} (hle : G ≤ G')
    (hG : MetaMathlibExt.IsHighlyHomogeneous G) :
    MetaMathlibExt.IsHighlyHomogeneous G' := by
  intro k
  constructor
  intro x y
  obtain ⟨g, hg⟩ := (hG k).exists_smul_eq x y
  refine ⟨⟨(g : Equiv.Perm α), hle g.2⟩, ?_⟩
  apply Subtype.ext
  have e1 : (((⟨(g : Equiv.Perm α), hle g.2⟩ : G') • x).val : Finset α)
      = (((g : G) • x).val : Finset α) := rfl
  rw [e1, hg]

end MetaMathlibExt.CameronSeparationHelpers
end

@[expose] public section

/-!
# Cameron separation group

The circular-order separation automorphism group is closed in the pointwise topology
and highly homogeneous.
-/

namespace MetaMathlibExt.CameronSeparationGroupWanted

/-- **The separation group of a countably infinite dense circular order is closed and highly
homogeneous.** Let $\alpha$ be a countably infinite set with a circular order, and write
$\operatorname{btw}(a, b, c)$ when $b$ lies between $a$ and $c$ going around from $a$ to $c$.
Suppose the circular order is dense: for all distinct $a, b \in \alpha$ there is some
$c \in \alpha$, different from $a$ and $b$, with $\operatorname{btw}(a, c, b)$. Then the
separation automorphism group of $\alpha$ is closed in the topology of pointwise convergence on
the permutations of $\alpha$, where $\alpha$ carries the discrete topology, and it is highly
homogeneous: for every natural number $k$ it has a single orbit on the $k$-element subsets of
$\alpha$.

Source: Daniele A. Gewurz and Francesca Merola, "Sequences realized as Parker vectors
of oligomorphic permutation groups," Journal of Integer Sequences 6,
`https://cs.uwaterloo.ca/journals/JIS/VOL6/Gewurz/gewurz22.tex`, lines 331–359. The
source identifies `D` (also `C*`) as the cyclic-order permutations preserving or
reversing the order and calls Cameron's five representatives closed and highly
homogeneous, glossed as one orbit on `k`-sets for all `k`. The source cites Peter J.
Cameron, "Transitivity of permutation groups on unordered sets," Math. Z. 148 (1976),
127–139. Interpretation boundary: only the `D` representative is asserted, not
exhaustive classification, uniqueness, or conjugacy. The explicit countability,
infinitude, and circular-density hypotheses select the intended countable dense
circular order.

Proves `Wanted` entry `separationAutSubgroup_isClosed_and_highlyHomogeneous`.
-/
public theorem separationAutSubgroup_isClosed_and_highlyHomogeneous
    {α : Type*} [DecidableEq α] [Countable α] [Infinite α] [CircularOrder α]
    (hdensity : ∀ a b : α, a ≠ b → ∃ c : α, btw a c b ∧ c ≠ a ∧ c ≠ b) :
    @IsClosed (Equiv.Perm α) (Equiv.Perm.pointwiseTopology (α := α))
        (↑(separationAutSubgroup α) : Set (Equiv.Perm α)) ∧
      IsHighlyHomogeneous (separationAutSubgroup α) := by
  have hdense' : ∀ a b : α, a ≠ b → ∃ c : α, c ≠ a ∧ c ≠ b ∧ btw a c b := by
    intro a b hab
    obtain ⟨c, hbtw, hca, hcb⟩ := hdensity a b hab
    exact ⟨c, hca, hcb, hbtw⟩
  have hcirc := circularOrderAutSubgroup_isClosed_and_highlyHomogeneous hdense'
  exact ⟨MetaMathlibExt.CameronSeparationHelpers.sep_isClosed_separationAutSubgroup,
    MetaMathlibExt.CameronSeparationHelpers.sep_highlyHomogeneous_mono
      (MetaMathlibExt.CameronSeparationHelpers.sep_circularOrder_le_separation α)
      hcirc.2⟩

end MetaMathlibExt.CameronSeparationGroupWanted
