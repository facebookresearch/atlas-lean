/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.ActiveEdgeDifferential

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.ActiveEdgeDifferential`

* `absorb_cross_complement` on explicit numbers `θ = 1/2`, `D = 1`, `κ = 1/2`, `cR = 1`,
  `θ' = 1`;
* `active_cross_one_sub_lower` on the complete graph on `Fin 2` with unit couplings, `q = 2`,
  `β = β₀ = 1`, an explicit edge embedding into `ℤ¹` and the empty target set;
* `geometricDenom_pos` for the Dirac mass at the all-closed configuration;
* `active_fk_differential_inequality` in its conditional form (geometric hypotheses as binders).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.ActiveEdgeDifferential

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.ActiveEdgeDifferential
open _root_.StatMech.Lattice _root_.StatMech.OSSS.AdaptiveCovLowerGeom
open _root_.StatMech.OSSS.RevealmentConstruction _root_.StatMech.OSSS.RevealmentTranslation

-- The absorption step on explicit numbers.
example : 0 < (1 : ℝ) * (1 / 2) ∧ (1 * (1 / 2)) * ((1 / 2 : ℝ) / 1) ≤ 1 :=
  absorb_cross_complement (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

-- Finite energy lower bound on `1 - θ` for `K₂` embedded in `ℤ¹`, with an empty target set.
example (o : Site 1) :
    (∏ e ∈ incidentEdges (fun _ : (⊤ : SimpleGraph (Fin 2)).edgeSet => (0 : Site 1))
        (fun _ => fun _ => 1) o, Real.exp (-(1 * (fun _ : Sym2 (Fin 2) => (1 : ℝ)) e.1))) ≤
      1 - Lindeberg.mean
        (FK.activeProb (⊤ : SimpleGraph (Fin 2)) (FK.betaParams (fun _ => 1) 1) 2)
        ((crossEvent (fun _ : (⊤ : SimpleGraph (Fin 2)).edgeSet =>
            s((0 : Site 1), fun _ => 1)) o ∅).indicator (fun _ => (1 : ℝ))) :=
  active_cross_one_sub_lower ⊤ (fun _ => 1) (fun _ => one_pos) 2 1 1 (by norm_num)
    one_pos le_rfl (fun _ => rfl) o ∅ (Set.notMem_empty o)

open Classical in
-- The geometric denominator is positive for a Dirac probability mass.
example (n : ℕ) (hn : 1 ≤ n) (Λ : Finset (Site 1)) (hne : Λ.Nonempty)
    (edge : Bool → Sym2 (Site 1)) :
    0 < 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n,
      Lindeberg.mean (fun ω : ConfigSpace Bool => if ω = fun _ => false then 1 else 0)
        (fun ω => if ConnectedToSet 1 (liftCfg edge ω) x (centeredBoundary x j)
          then (1 : ℝ) else 0)) / (n : ℝ) :=
  geometricDenom_pos _ (fun ω => by split_ifs <;> norm_num)
    (by rw [Finset.sum_ite_eq']; simp) edge n hn Λ hne

-- The OSSS differential inequality, conditional on its geometric hypotheses.
example {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]
    (J : Sym2 V → ℝ) (hJ : ∀ e, 0 < J e) (β : ℝ) (hβ : 0 < β)
    {edge : G.edgeSet → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : G.edgeSet → Site d}
    (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List G.edgeSet) (hl : ∀ e, e ∈ l)
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k) (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (n : ℕ) (hn : 1 ≤ n) (Λ : Finset (Site d)) (hne : Λ.Nonempty)
    (hLu : ∀ e : G.edgeSet, endU e ∈ Λ) (hLv : ∀ e : G.edgeSet, endV e ∈ Λ)
    (hUbox : ∀ e : G.edgeSet, endU e ∈ box d n) (hVbox : ∀ e : G.edgeSet, endV e ∈ box d n) :=
  active_fk_differential_inequality G J hJ 2 β β (by norm_num) hβ le_rfl hinj hcoh hadj o l hl
    disc₀ hdisc₀sub hdisc₀sup hoB ho n hn Λ hne hLu hLv hUbox hVbox

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.ActiveEdgeDifferential
