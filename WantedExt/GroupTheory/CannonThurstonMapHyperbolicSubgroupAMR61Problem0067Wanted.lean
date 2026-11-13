/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cannon–Thurston maps for hyperbolic subgroups (Kapovich, Problem 67)

M. Kapovich, Problems on boundaries of groups and Kleinian groups, Problem 67 (Mahan Mitra): let `H
⊂ G` be a hyperbolic subgroup of a hyperbolic group (we do not assume that `H` is quasiconvex). Is
it true that there exists an equivariant continuous map `∂∞H → ∂∞G`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GroupTheory.HyperbolicGroup

@[expose] public section

namespace MathlibExt.GroupTheory.CannonThurstonMapHyperbolicSubgroupAMR61Problem0067Wanted

/-!
Source: M. Kapovich, Problems on boundaries of groups and Kleinian groups (collected at a 2005 AIM
workshop), Problem 67 (M. Mitra). UnsolvedMath record UM-06200067 (`AMR-061-0067`), dataset
ulamai/UnsolvedMath v1.8.0.

The map asked for is the Cannon–Thurston map, the boundary map induced by the inclusion `H → G` (the
list's Problem 66 calls such a map a Cannon–Thurston map, and Baker–Riley §1 state Mitra's question
as whether the map `∂H → ∂G` induced from the inclusion is always well defined). Boundaries are
sequential, as in Baker–Riley §1: a sequence converges at infinity when its Gromov products `(a_m ·
a_n)₁` at the identity tend to infinity as `m, n → ∞`, and two such sequences define the same
boundary point when `(a_m · b_n)₁ → ∞`; Baker–Riley note that this boundary does not depend on the
finite generating set. `InducesBoundaryMap H P Q` says that the inclusion sends convergent sequences
to convergent sequences and equivalent ones to equivalent ones, i.e. that the induced map is well
defined; the metric is the word metric `Group.Generators.normedGroup` used by `Group.IsHyperbolic`.
The generating families of `G` and `H` are existentially quantified, which only weakens the claim
refuted.
-/

open Filter

/-- The Gromov product `(x · y)₁ = (|x| + |y| - d(x, y)) / 2` at the identity, for the word metric
`Group.Generators.normedGroup` of the generating family `P` (the metric of `Group.IsHyperbolic`). -/
noncomputable def gromovProductAtOne {G ι : Type*} [Group G] (P : Group.Generators G ι)
    (x y : G) : ℝ :=
  @Metric.gromovProduct G P.normedGroup.toMetricSpace.toPseudoMetricSpace 1 x y

/-- The sequence `u` converges at infinity (to a point of the Gromov boundary) for the word metric
of `P`: `(u m · u n)₁ → ∞` as `m, n → ∞`. -/
def ConvergesAtInfinity {G ι : Type*} [Group G] (P : Group.Generators G ι) (u : ℕ → G) : Prop :=
  Tendsto (fun p : ℕ × ℕ => gromovProductAtOne P (u p.1) (u p.2)) atTop atTop

/-- Two sequences define the same boundary point for the word metric of `P`: `(u m · v n)₁ → ∞`
as `m, n → ∞`. -/
def EquivAtInfinity {G ι : Type*} [Group G] (P : Group.Generators G ι) (u v : ℕ → G) : Prop :=
  Tendsto (fun p : ℕ × ℕ => gromovProductAtOne P (u p.1) (v p.2)) atTop atTop

/-- The inclusion of the subgroup `H` induces a well-defined map `∂H → ∂G` of Gromov boundaries
(the Cannon–Thurston map), with `∂H` taken for the generating family `Q` of `H` and `∂G` for the
generating family `P` of `G`: every sequence of `H` converging at infinity in `H` converges at
infinity in `G`, and sequences defining the same point of `∂H` define the same point of `∂G`. -/
def InducesBoundaryMap {G ι κ : Type*} [Group G] (H : Subgroup G) (P : Group.Generators G ι)
    (Q : Group.Generators H κ) : Prop :=
  (∀ u : ℕ → H, ConvergesAtInfinity Q u → ConvergesAtInfinity P fun n => (u n : G)) ∧
    ∀ u v : ℕ → H, ConvergesAtInfinity Q u → ConvergesAtInfinity Q v → EquivAtInfinity Q u v →
      EquivAtInfinity P (fun n => (u n : G)) fun n => (v n : G)

/-- Mitra's question (Kapovich, Problem 67): for every hyperbolic subgroup `H` of a hyperbolic
group `G` (not assumed quasiconvex) the inclusion induces a map `∂H → ∂G`, for some finite
generating families of `G` and `H`. -/
def cannonThurstonMapExists : Prop :=
  ∀ (G : Type) [Group G] (H : Subgroup G), Group.IsHyperbolic G → Group.IsHyperbolic H →
    ∃ (ι κ : Type) (_ : Finite ι) (_ : Finite κ) (P : Group.Generators G ι)
      (Q : Group.Generators H κ), InducesBoundaryMap H P Q

/--
Resolved false: Baker and Riley construct a hyperbolic group `G` with a free subgroup `H` of rank 3
(hence hyperbolic) for which the inclusion induces no map `∂H → ∂G`, i.e. there is no
Cannon–Thurston map. Source: M. Kapovich, Problems on boundaries of groups and Kleinian groups
(collected at a 2005 AIM workshop), Problem 67 (M. Mitra); resolution: O. Baker and T. R. Riley,
Cannon–Thurston maps do not always exist, Forum Math. Sigma 1 (2013), e3, DOI 10.1017/fms.2013.4,
arXiv:1206.0505, §1: Mitra asks whether the map ∂H → ∂G induced from the inclusion is always well
defined, a question appearing in the problem lists [3] and [15] ([15] = Kapovich's list); 'We answer
it negatively: Theorem 1': for suitable positive words the group G = ⟨a, b, c1, c2, d1, d2 |
relations of Theorem 1⟩ is hyperbolic, the subgroup H = ⟨b, d1, d2⟩ is free of rank 3, and there is
no Cannon–Thurston map ∂H → ∂G, https://arxiv.org/abs/1206.0505.
-/
public theorem_wanted cannonThurstonMapExists_refuted : ¬ cannonThurstonMapExists

end MathlibExt.GroupTheory.CannonThurstonMapHyperbolicSubgroupAMR61Problem0067Wanted
