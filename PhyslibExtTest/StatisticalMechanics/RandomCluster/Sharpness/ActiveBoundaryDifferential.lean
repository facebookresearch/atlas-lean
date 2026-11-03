/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.ActiveBoundaryDifferential

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.ActiveBoundaryDifferential`

* `cov_activeBC_eq` on the complete graph on `Fin 2` with the empty boundary graph;
* `activeBC_cross_one_sub_lower` on `K₂` with boundary graph `⊥`, unit couplings, `q = 2`,
  `β = β₀ = 1`, an explicit edge embedding into `ℤ¹` and the empty target set;
* `activeBC_fk_differential_logistic` and `activeBC_fk_differential_inequality` in their
  conditional forms (geometric hypotheses as binders).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.ActiveBoundaryDifferential

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.ActiveBoundaryDifferential
open _root_.StatMech.OSSS.ActiveEdgeDifferential
open _root_.StatMech.Lattice _root_.StatMech.OSSS.AdaptiveCovLowerGeom
open _root_.StatMech.OSSS.RevealmentConstruction _root_.StatMech.OSSS.RevealmentTranslation

-- The boundary-conditioned covariance agrees with the generic Lindeberg covariance.
example (f g : ConfigSpace (⊤ : SimpleGraph (Fin 2)).edgeSet → ℝ) :
    Lindeberg.cov (FK.activeBCProb (⊤ : SimpleGraph (Fin 2)) ⊥ (fun _ => 1 / 2) 2) f g =
      FK.activeBCCov (⊤ : SimpleGraph (Fin 2)) ⊥ (fun _ => 1 / 2) 2 f g :=
  cov_activeBC_eq ⊤ ⊥ _ 2 f g

-- Finite energy lower bound on `1 - θ` for `K₂` with boundary graph `⊥`, empty target set.
example (o : Site 1) :
    (incidentEdges (fun _ : (⊤ : SimpleGraph (Fin 2)).edgeSet => (0 : Site 1))
        (fun _ => fun _ => 1) o).prod
        (fun e => Real.exp (-(1 * (fun _ : Sym2 (Fin 2) => (1 : ℝ)) e.1))) ≤
      1 - Lindeberg.mean
        (FK.activeBCProb (⊤ : SimpleGraph (Fin 2)) ⊥ (FK.betaParams (fun _ => 1) 1) 2)
        ((crossEvent (fun _ : (⊤ : SimpleGraph (Fin 2)).edgeSet =>
            s((0 : Site 1), fun _ => 1)) o ∅).indicator (fun _ => (1 : ℝ))) :=
  activeBC_cross_one_sub_lower ⊤ ⊥ (fun _ => 1) (fun _ => one_pos) 2 1 1 (by norm_num)
    one_pos le_rfl (fun _ => rfl) o ∅ (Set.notMem_empty o)

-- The logistic inequality, conditional on its geometric hypotheses.
example {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]
    (C : SimpleGraph V) [DecidableRel C.Adj]
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
  activeBC_fk_differential_logistic G C J hJ 2 β (by norm_num) hβ hinj hcoh hadj o l hl
    disc₀ hdisc₀sub hdisc₀sup hoB ho n hn Λ hne hLu hLv hUbox hVbox

-- The OSSS differential inequality, conditional on its geometric hypotheses.
example {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]
    (C : SimpleGraph V) [DecidableRel C.Adj]
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
  activeBC_fk_differential_inequality G C J hJ 2 β β (by norm_num) hβ le_rfl hinj hcoh hadj o
    l hl disc₀ hdisc₀sub hdisc₀sup hoB ho n hn Λ hne hLu hLv hUbox hVbox

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.ActiveBoundaryDifferential
