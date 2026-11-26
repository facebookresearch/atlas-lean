/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Topology/KirkNormalStructure.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), manifest `manifests/problems/kirk_normal_structure.toml`
(revision 1, submitted by Kim Morrison, archived).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

The adapted portions are the definitions of diameter, point radius, diametral point, normal
structure and nonexpansive self-map, and the statement of Kirk's theorem. They were namespaced
and documented in `WantedExt/Topology/KirkNormalStructureWanted.lean` and moved here with their
names and statements intact. The proof is original to ATLAS. lean-eval ships no `NOTICE` file.

Unless required by applicable law or agreed to in writing, software distributed under the
License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied. See the License for the specific language governing permissions
and limitations under the License.
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Order.Zorn

/-!
# Kirk's normal-structure fixed-point theorem

`kirk_normal_structure` gives a fixed point of a nonexpansive self-map on a nonempty closed
bounded convex set with normal structure in a reflexive real Banach space.
-/

@[expose] public section

namespace MathlibExt.Topology.KirkNormalStructureWanted
namespace Topology.KirkNormalStructure

open Function Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option linter.dupNamespace false in
/-- **Diameter of a set.** The diameter of a set $s$ in a real normed space is the supremum in
$\mathbb{R}$ of the distances $\operatorname{dist}(x, y)$ over all $x, y \in s$; by the convention
for real suprema it is $0$ when $s$ is empty or these distances are unbounded. -/
noncomputable def metricDiameter (s : Set E) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ s, ∃ y ∈ s, dist x y = r}

set_option linter.dupNamespace false in
/-- **Radius of a point in a set.** The radius of a point $x$ in a set $s$ of a real normed space
is the supremum in $\mathbb{R}$ of the distances $\operatorname{dist}(x, y)$ over all $y \in s$; by
the convention for real suprema it is $0$ when $s$ is empty or these distances are unbounded. -/
noncomputable def pointRadiusIn (x : E) (s : Set E) : ℝ :=
  sSup {r : ℝ | ∃ y ∈ s, dist x y = r}

set_option linter.dupNamespace false in
/-- **Diametral point.** A point $x$ of a real normed space is diametral in a set $s$
if $x \in s$ and the radius of $x$ in $s$ equals the diameter of $s$. -/
def IsDiametralPoint (s : Set E) (x : E) : Prop :=
  x ∈ s ∧ pointRadiusIn x s = metricDiameter s

set_option linter.dupNamespace false in
/-- **Normal structure.** A set $K$ in a real normed space has normal structure if every convex
subset $H \subseteq K$ with at least two points contains a point that is not diametral in $H$. -/
def HasNormalStructure (K : Set E) : Prop :=
  ∀ H : Set E,
    H ⊆ K →
      Convex ℝ H →
        H.Nontrivial →
          ∃ x ∈ H, ¬ IsDiametralPoint H x

set_option linter.dupNamespace false in
/-- **Nonexpansive self-map.** A map $T : K \to K$ from a subset $K$ of a real normed space to
itself is nonexpansive if $\|T(x) - T(y)\| \le \|x - y\|$ for all $x, y \in K$, that is, if $T$
is $1$-Lipschitz for the distance inherited from the space. -/
def IsNonexpansiveSelfMap (K : Set E) (T : K → K) : Prop :=
  LipschitzWith 1 T

private structure InvariantSubset (K : Set E) (f : E → E) (s : Set E) : Prop where
  subset : s ⊆ K
  nonempty : s.Nonempty
  closed : IsClosed s
  convex : Convex ℝ s
  invariant : MapsTo f s s

private theorem weaklyClosed {s : Set E} (hs : IsClosed s) (hc : Convex ℝ s) :
    IsClosed (toWeakSpace ℝ E '' s) := by
  rw [← closure_eq_iff_isClosed, ← hc.toWeakSpace_closure ℝ, hs.closure_eq]

private theorem weaklyCompact {s : Set E} (hs : IsClosed s) (hc : Convex ℝ s)
    (hb : Bornology.IsBounded s)
    (href : Surjective (NormedSpace.inclusionInDoubleDual ℝ E)) :
    IsCompact (toWeakSpace ℝ E '' s) := by
  rw [← (weaklyClosed hs hc).closure_eq]
  apply NormedSpace.isCompact_closure_of_isBounded
  · simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ E).injective] using hb
  · intro φ _
    obtain ⟨x, hx⟩ := href (WeakDual.toStrongDual φ)
    exact ⟨toWeakSpace ℝ E x, congrArg StrongDual.toWeakDual hx⟩

private theorem exists_minimal_invariant {K : Set E} {f : E → E}
    (hK : InvariantSubset K f K) (hcompact : IsCompact (toWeakSpace ℝ E '' K)) :
    ∃ H, Minimal (InvariantSubset K f) H := by
  suffices ∃ H, H ⊆ K ∧ Minimal (InvariantSubset K f) H by
    obtain ⟨H, _, hH⟩ := this
    exact ⟨H, hH⟩
  apply zorn_superset_nonempty {s | InvariantSubset K f s} _ K hK
  intro c hsub hchain hne
  have h (s : c) : InvariantSubset K f s.1 := hsub s.2
  let w (s : c) := toWeakSpace ℝ E '' s.1
  have hclosed (s : c) : IsClosed (w s) := weaklyClosed (h s).closed (h s).convex
  have : Nonempty c := hne.coe_sort
  have hinter : (⋂ s, w s).Nonempty := by
    apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    · intro i j
      obtain hij | hji := hchain.total i.prop j.prop
      · exact ⟨i, Subset.rfl, image_mono hij⟩
      · exact ⟨j, image_mono hji, Subset.rfl⟩
    · exact fun s ↦ (h s).nonempty.image _
    · exact fun s ↦ hcompact.of_isClosed_subset (hclosed s) (image_mono (h s).subset)
    · exact hclosed
  obtain ⟨x, hx⟩ := hinter
  obtain ⟨s, hs⟩ := hne
  refine ⟨⋂₀ c, ⟨(sInter_subset_of_mem hs).trans (h ⟨s, hs⟩).subset, ?_, ?_, ?_, ?_⟩,
    fun _ ht ↦ sInter_subset_of_mem ht⟩
  · refine ⟨(toWeakSpace ℝ E).symm x, mem_sInter.mpr fun t ht ↦ ?_⟩
    exact (Set.mem_image_equiv (f := (toWeakSpace ℝ E).toEquiv)).mp (mem_iInter.mp hx ⟨t, ht⟩)
  · exact isClosed_sInter fun t ht ↦ (h ⟨t, ht⟩).closed
  · exact convex_sInter fun t ht ↦ (h ⟨t, ht⟩).convex
  · intro y hy
    exact mem_sInter.mpr fun t ht ↦ (h ⟨t, ht⟩).invariant (mem_sInter.mp hy t ht)

-- Minimality first implies that the closed convex hull of the image fills H.
private theorem hull_image_eq {K H : Set E} {f : E → E}
    (hm : Minimal (InvariantSubset K f) H) : closedConvexHull ℝ (f '' H) = H := by
  have h := hm.prop
  have hsub := closedConvexHull_min h.invariant.image_subset h.convex h.closed
  apply hm.eq_of_subset _ hsub
  exact ⟨hsub.trans h.subset, (h.nonempty.image f).mono subset_closedConvexHull,
    isClosed_closedConvexHull, convex_closedConvexHull,
    fun x hx ↦ subset_closedConvexHull (mem_image_of_mem f (hsub hx))⟩

-- A second application of minimality makes every point of H diametral.
private theorem diametral_of_minimal {K H : Set E} {f : E → E}
    (hm : Minimal (InvariantSubset K f) H) (hb : Bornology.IsBounded H)
    (hf : ∀ x ∈ H, ∀ y ∈ H, dist (f x) (f y) ≤ dist x y)
    {a : E} (ha : a ∈ H) : IsDiametralPoint H a := by
  let r := pointRadiusIn a H
  have hdist (x y : E) (hx : x ∈ H) (hy : y ∈ H) :=
    Metric.dist_le_diam_of_mem hb hx hy
  have har (y : E) (hy : y ∈ H) : dist a y ≤ r := by
    apply le_csSup _ (show dist a y ∈ {d : ℝ | ∃ z ∈ H, dist a z = d} from ⟨y, hy, rfl⟩)
    exact ⟨Metric.diam H, fun _ ⟨z, hz, e⟩ ↦ e ▸ hdist a z ha hz⟩
  -- The centers of radius r form a nonempty closed convex subset of H.
  let C := H ∩ ⋂ z : H, Metric.closedBall (z : E) r
  have center {x : E} : x ∈ C ↔ x ∈ H ∧ ∀ y ∈ H, dist x y ≤ r := by
    simp [C, Metric.mem_closedBall]
  have h := hm.prop
  have hinv : MapsTo f C C := by
    intro x hx
    obtain ⟨hxH, hxr⟩ := center.mp hx
    refine center.mpr ⟨h.invariant hxH, fun y hy ↦ ?_⟩
    -- The ball about f x contains the image of H, hence its closed convex hull.
    have himage : f '' H ⊆ Metric.closedBall (f x) r := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hf z hz x hxH).trans (dist_comm x z ▸ hxr z hz)
    have hball := closedConvexHull_min himage (convex_closedBall _ _) Metric.isClosed_closedBall
    rw [hull_image_eq hm] at hball
    exact dist_comm y (f x) ▸ hball hy
  have heq : C = H := hm.eq_of_subset
    ⟨inter_subset_left.trans h.subset, ⟨a, center.mpr ⟨ha, har⟩⟩,
      h.closed.inter (isClosed_iInter fun _ ↦ Metric.isClosed_closedBall),
      h.convex.inter (convex_iInter fun _ ↦ convex_closedBall _ _), hinv⟩ inter_subset_left
  refine ⟨ha, le_antisymm ?_ ?_⟩
  · unfold pointRadiusIn metricDiameter
    refine csSup_le ⟨dist a a, a, ha, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    apply le_csSup _ (show dist a y ∈ {d : ℝ | ∃ x ∈ H, ∃ z ∈ H, dist x z = d} from
      ⟨a, ha, y, hy, rfl⟩)
    exact ⟨Metric.diam H, fun _ ⟨x, hx, z, hz, e⟩ ↦ e ▸ hdist x z hx hz⟩
  · unfold metricDiameter
    refine csSup_le ⟨dist a a, a, ha, a, ha, rfl⟩ ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact (center.mp (heq.symm ▸ hx)).2 y hy

set_option linter.dupNamespace false in
/-- **Kirk's fixed-point theorem for sets with normal structure.** Let $E$ be a reflexive real
Banach space, meaning that the canonical embedding of $E$ into its double dual is surjective, and
let $K \subseteq E$ be a nonempty, closed, bounded, convex set with normal structure. Then every
nonexpansive self-map $T : K \to K$ has a fixed point.

Source: W. A. Kirk, A fixed point theorem for mappings which do not increase distances, Amer. Math.
Monthly 72 (1965). Listed as §228 in O. Knill, Some Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §228. Via
leanprover/lean-eval@38361be, problem `kirk_normal_structure`. -/
public theorem kirk_normal_structure [CompleteSpace E]
    (hE_reflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (K : Set E) (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK_bounded : Bornology.IsBounded K) (hK_convex : Convex ℝ K)
    (hK_normal : HasNormalStructure K) (T : K → K)
    (hT : IsNonexpansiveSelfMap K T) :
    ∃ x : K, IsFixedPt T x := by
  classical
  let f (x : E) : E := if hx : x ∈ K then (T ⟨x, hx⟩ : E) else x
  have hf {x : E} (hx : x ∈ K) : f x = (T ⟨x, hx⟩ : E) := dite_eq_left hx
  have hmaps : MapsTo f K K := fun x hx ↦ (hf hx).symm ▸ (T ⟨x, hx⟩).prop
  obtain ⟨H, hm⟩ := exists_minimal_invariant
    ⟨Subset.rfl, hK_nonempty, hK_closed, hK_convex, hmaps⟩
    (weaklyCompact hK_closed hK_convex hK_bounded hE_reflexive)
  have h := hm.prop
  obtain hsingle | hnon := H.subsingleton_or_nontrivial
  · obtain ⟨x, hx⟩ := h.nonempty
    refine ⟨⟨x, h.subset hx⟩, Subtype.ext ?_⟩
    exact (hf (h.subset hx)).symm.trans (hsingle (h.invariant hx) hx)
  · obtain ⟨a, ha, hnd⟩ := hK_normal H h.subset h.convex hnon
    refine (hnd (diametral_of_minimal hm (hK_bounded.subset h.subset) ?_ ha)).elim
    intro x hx y hy
    rw [hf (h.subset hx), hf (h.subset hy)]
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using
      hT.dist_le_mul ⟨x, h.subset hx⟩ ⟨y, h.subset hy⟩

end Topology.KirkNormalStructure

end MathlibExt.Topology.KirkNormalStructureWanted
