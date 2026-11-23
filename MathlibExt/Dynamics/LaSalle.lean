/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Dynamics.Flow
public import Mathlib.Dynamics.OmegaLimit
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# LaSalle's invariance principle

Let `ϕ` be a continuous semiflow on a Hausdorff space `X` (a `Flow` of the time monoid `ℝ≥0`,
for example the solution semiflow of an autonomous ODE on a positively invariant set), and let
`V : X → ℝ` be continuous. If the forward orbit of `x` stays in a compact set `K` and `V` is
nonincreasing along it, then:

* the ω-limit set `ω⁺(x)` is nonempty, and `V` is constant on it and along every orbit that
  starts in it;
* consequently, if `E` is a set containing every point `y ∈ K` whose orbit keeps `V` constant
  (`V(ϕ t y) = V y` for all `t`), then `ω⁺(x)` lies in `M = {y | ∀ t, ϕ t y ∈ E}`, the largest
  forward-invariant subset of `E`, and the orbit of `x` eventually enters every open
  neighbourhood of `M`.

For an ODE `x' = f(x)` with `C¹` Lyapunov function `V`, a point whose orbit keeps `V` constant
has `V̇ = ∇V · f = 0` along that orbit, so `E = {y ∈ K | V̇(y) = 0}` qualifies and this is the
classical statement: every solution in a compact positively invariant set approaches the
largest invariant set in `{V̇ = 0}`.

## Main results

* `Flow.exists_forall_eq_of_mem_omegaLimit`: `V` is constant on `ω⁺(x)` and along orbits from
  it.
* `Flow.lasalle`: LaSalle's invariance principle (inclusion in the largest forward-invariant
  subset of `E`, nonemptiness, and attraction).

## References

* J. P. LaSalle, *Some extensions of Liapunov's second method*, IRE Trans. Circuit Theory 7
  (1960) 520–527.
* J. P. LaSalle, *The Stability of Dynamical Systems*, CBMS-NSF Regional Conf. Ser. Appl.
  Math. 25, SIAM (1976), Ch. 2.
* H. K. Khalil, *Nonlinear Systems*, 3rd ed., Prentice Hall (2002), §4.2, Theorem 4.4.
-/

@[expose] public section

open Filter Set Topology
open scoped NNReal omegaLimit

namespace Flow

variable {X : Type*} [TopologicalSpace X]

/-- The ω-limit set of a point under a semiflow is contained in every closed set that contains
the forward orbit. -/
theorem omegaLimit_singleton_subset_of_isClosed (ϕ : Flow ℝ≥0 X) {x : X} {K : Set X}
    (hK : IsClosed K) (hxK : ∀ t, ϕ t x ∈ K) : ω⁺ ϕ {x} ⊆ K := by
  refine (omegaLimit_subset_closure_image2 atTop ϕ {x} univ_mem).trans ?_
  refine closure_minimal ?_ hK
  rintro _ ⟨t, -, y, rfl, rfl⟩
  exact hxK t

/-- **`V` is constant on the ω-limit set.** If the forward orbit of `x` lies in a compact set
`K` and the continuous function `V` is nonincreasing along it, then there is a constant `c`
(the limit of `V(ϕ t x)`) such that `V(ϕ t y) = c` for every `y ∈ ω⁺(x)` and every `t ≥ 0`. -/
theorem exists_forall_eq_of_mem_omegaLimit (ϕ : Flow ℝ≥0 X) {V : X → ℝ}
    (hV : Continuous V) {x : X} {K : Set X} (hK : IsCompact K) (hxK : ∀ t, ϕ t x ∈ K)
    (hanti : Antitone fun t => V (ϕ t x)) :
    ∃ c : ℝ, ∀ y ∈ ω⁺ ϕ {x}, ∀ t, V (ϕ t y) = c := by
  have hbdd : BddBelow (range fun t => V (ϕ t x)) := by
    obtain ⟨m, hm⟩ := (hK.image hV).bddBelow
    exact ⟨m, by rintro _ ⟨t, rfl⟩; exact hm ⟨_, hxK t, rfl⟩⟩
  have key : ∀ y ∈ ω⁺ ϕ {x}, V y = ⨅ t, V (ϕ t x) := by
    intro y hy
    have hmem : ∀ T : ℝ≥0, V y ∈ Icc (⨅ t, V (ϕ t x)) (V (ϕ T x)) := by
      intro T
      have hy' := omegaLimit_subset_closure_image2 atTop ϕ {x} (Ici_mem_atTop T) hy
      have hcl : closure (image2 ϕ (Ici T) {x}) ⊆ V ⁻¹' Icc (⨅ t, V (ϕ t x)) (V (ϕ T x)) := by
        refine closure_minimal ?_ (isClosed_Icc.preimage hV)
        rintro _ ⟨t, ht, z, rfl, rfl⟩
        exact ⟨ciInf_le hbdd t, hanti ht⟩
      exact hcl hy'
    exact le_antisymm (le_ciInf fun T => (hmem T).2) (hmem 0).1
  refine ⟨⨅ t, V (ϕ t x), fun y hy t => key _ ?_⟩
  exact ϕ.isInvariant_omegaLimit atTop {x}
    (fun _ => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id) t hy

/-- **LaSalle's invariance principle** (LaSalle 1960; Khalil 2002, Theorem 4.4). Let the forward
orbit of `x` under the semiflow `ϕ` lie in a compact set `K`, let `V` be continuous and
nonincreasing along that orbit, and let `E` contain every `y ∈ K` whose orbit keeps `V`
constant. Then the ω-limit set `ω⁺(x)` is nonempty and contained in the largest
forward-invariant subset `M = {y | ∀ t, ϕ t y ∈ E}` of `E`, and the orbit of `x` eventually
enters every open set containing `M`. -/
theorem lasalle [T2Space X] (ϕ : Flow ℝ≥0 X) {V : X → ℝ} (hV : Continuous V) {x : X}
    {K E : Set X} (hK : IsCompact K) (hxK : ∀ t, ϕ t x ∈ K)
    (hanti : Antitone fun t => V (ϕ t x))
    (hE : ∀ y ∈ K, (∀ t, V (ϕ t y) = V y) → y ∈ E) :
    (ω⁺ ϕ {x}).Nonempty ∧ ω⁺ ϕ {x} ⊆ {y | ∀ t, ϕ t y ∈ E} ∧
      ∀ U : Set X, IsOpen U → {y | ∀ t, ϕ t y ∈ E} ⊆ U → ∀ᶠ t in atTop, ϕ t x ∈ U := by
  obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_omegaLimit ϕ hV hK hxK hanti
  have hωK : ω⁺ ϕ {x} ⊆ K := omegaLimit_singleton_subset_of_isClosed ϕ hK.isClosed hxK
  have hinv := ϕ.isInvariant_omegaLimit atTop {x}
    (fun _ => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id)
  have hsub : ω⁺ ϕ {x} ⊆ {y | ∀ t, ϕ t y ∈ E} := by
    intro y hy t
    refine hE _ (hωK (hinv t hy)) fun s => ?_
    rw [← ϕ.map_add, hc _ hy, hc _ hy]
  have habs : ∀ᶠ t in atTop, MapsTo (ϕ t) {x} K :=
    Eventually.of_forall fun t z hz => by rw [hz]; exact hxK t
  refine ⟨nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x} hK
    ⟨univ, univ_mem, closure_minimal ?_ hK.isClosed⟩ (singleton_nonempty x), hsub,
    fun U hU hMU => ?_⟩
  · rintro _ ⟨t, -, z, rfl, rfl⟩
    exact hxK t
  · exact (eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset atTop ϕ {x}
      hK habs hU (hsub.trans hMU)).mono fun t ht => ht rfl

end Flow
