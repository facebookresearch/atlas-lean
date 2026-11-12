/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.ActiveBoundaryEdges
import Code.FK.EdgeConfigZ
import Code.FK.IvProperties

open scoped BigOperators Classical
open Finset

namespace StatMech
namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (C : SimpleGraph V) [DecidableRel C.Adj]


def restrictActive (omega : ConfigSpace (Sym2 V)) : ConfigSpace G.edgeSet :=
  fun e => omega e.1

@[simp] theorem restrictActive_extendActive (omega : ConfigSpace G.edgeSet) :
    restrictActive G (extendActive G omega) = omega := by
  funext e
  exact extendActive_apply G omega e


noncomputable def activeSplitEquiv :
    ConfigSpace (Sym2 V) ≃
      ConfigSpace G.edgeSet × ConfigSpace {e : Sym2 V // e ∉ G.edgeSet} :=
  Equiv.piEquivPiSubtypeProd (fun e : Sym2 V => e ∈ G.edgeSet) (fun _ => Bool)

@[simp] theorem restrictActive_activeSplitEquiv_symm
    (eta : ConfigSpace G.edgeSet)
    (xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet}) :
    restrictActive G ((activeSplitEquiv G).symm (eta, xi)) = eta := by
  funext e
  simp [restrictActive, activeSplitEquiv,
    Equiv.piEquivPiSubtypeProd_symm_apply, e.2]

theorem numClustersBC_eq_of_edges
    (omega eta : ConfigSpace (Sym2 V))
    (h : ∀ e ∈ G.edgeFinset, omega e = eta e) :
    numClustersBC G C omega = numClustersBC G C eta := by
  unfold numClustersBC
  rw [ecz_openSub_eq_of_edges G omega eta h]

theorem bcWeight_eq_of_edges (p q : Real)
    (omega eta : ConfigSpace (Sym2 V))
    (h : ∀ e ∈ G.edgeFinset, omega e = eta e) :
    bcWeight G C p q omega = bcWeight G C p q eta := by
  unfold bcWeight
  rw [numClustersBC_eq_of_edges G C omega eta h]
  congr 1
  unfold edgeProduct
  exact Finset.prod_congr rfl fun e he => by rw [h e he]

theorem activeBCWeight_const_eq_bcWeight (p q : Real)
    (omega : ConfigSpace G.edgeSet) :
    activeBCWeight G C (fun _ => p) q omega =
      bcWeight G C p q (extendActive G omega) := by
  rfl

theorem bcWeight_activeSplitEquiv_symm (p q : Real)
    (eta : ConfigSpace G.edgeSet)
    (xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet}) :
    bcWeight G C p q ((activeSplitEquiv G).symm (eta, xi)) =
      activeBCWeight G C (fun _ => p) q eta := by
  rw [activeBCWeight_const_eq_bcWeight]
  apply bcWeight_eq_of_edges G C
  intro e he
  have heSet : e ∈ G.edgeSet := by
    rw [← SimpleGraph.mem_edgeFinset]
    exact he
  rw [show ((activeSplitEquiv G).symm (eta, xi)) e = eta ⟨e, heSet⟩ by
      simp [activeSplitEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, heSet]]
  exact (extendActive_apply G eta ⟨e, heSet⟩).symm

theorem card_inactive_config :
    Fintype.card (ConfigSpace {e : Sym2 V // e ∉ G.edgeSet}) =
      2 ^ ecz_NE G := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype]
  unfold ecz_NE
  congr 2
  ext e
  simp [SimpleGraph.mem_edgeFinset]



theorem activeBCZ_factorization (p q : Real) :
    bcZ G C p q = 2 ^ ecz_NE G * activeBCZ G C (fun _ => p) q := by
  rw [bcZ, ← Equiv.sum_comp (activeSplitEquiv G).symm
    (fun omega => bcWeight G C p q omega), Fintype.sum_prod_type]
  have key : forall eta : ConfigSpace G.edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
        bcWeight G C p q ((activeSplitEquiv G).symm (eta, xi))) =
      2 ^ ecz_NE G * activeBCWeight G C (fun _ => p) q eta := by
    intro eta
    rw [Finset.sum_congr rfl fun xi _ => bcWeight_activeSplitEquiv_symm G C p q eta xi]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_inactive_config G]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun eta _ => key eta, ← Finset.mul_sum]
  rfl

theorem activeBCNumer_factorization (p q : Real)
    (f : ConfigSpace G.edgeSet -> Real) :
    (∑ omega : ConfigSpace (Sym2 V),
      f (restrictActive G omega) * bcWeight G C p q omega) =
      2 ^ ecz_NE G * activeBCNumer G C (fun _ => p) q f := by
  rw [← Equiv.sum_comp (activeSplitEquiv G).symm
    (fun omega => f (restrictActive G omega) * bcWeight G C p q omega),
    Fintype.sum_prod_type]
  have key : forall eta : ConfigSpace G.edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
        f (restrictActive G ((activeSplitEquiv G).symm (eta, xi))) *
          bcWeight G C p q ((activeSplitEquiv G).symm (eta, xi))) =
      2 ^ ecz_NE G * (f eta * activeBCWeight G C (fun _ => p) q eta) := by
    intro eta
    rw [Finset.sum_congr rfl fun xi _ => by
      rw [restrictActive_activeSplitEquiv_symm,
        bcWeight_activeSplitEquiv_symm G C p q eta xi]]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_inactive_config G]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun eta _ => key eta, ← Finset.mul_sum]
  rfl



theorem activeBCMean_eq_bcProb_lift {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (f : ConfigSpace G.edgeSet -> Real) :
    activeBCMean G C (fun _ => p) q f =
      ∑ omega : ConfigSpace (Sym2 V),
        f (restrictActive G omega) * bcProb G C p q omega := by
  have htwo : (2 : Real) ^ ecz_NE G ≠ 0 := by positivity
  have hZactive : activeBCZ G C (fun _ => p) q ≠ 0 :=
    (activeBCZ_pos G C (fun _ => hp) (fun _ => hp1) hq).ne'
  rw [activeBCMean_eq_div]
  unfold bcProb
  rw [show (fun omega : ConfigSpace (Sym2 V) =>
      f (restrictActive G omega) *
        (bcWeight G C p q omega / bcZ G C p q)) =
      (fun omega =>
        (f (restrictActive G omega) * bcWeight G C p q omega) /
          bcZ G C p q) by funext omega; ring]
  rw [← Finset.sum_div, activeBCNumer_factorization G C,
    activeBCZ_factorization G C]
  field_simp

theorem activeBCProbOf_eq_bcProb_preimage {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace G.edgeSet)) :
    activeBCProbOf G C (fun _ => p) q A =
      ∑ omega : ConfigSpace (Sym2 V),
        (restrictActive G ⁻¹' A).indicator (fun _ => (1 : Real)) omega *
          bcProb G C p q omega := by
  rw [activeBCProbOf, activeBCMean_eq_bcProb_lift G C hp hp1 hq]
  apply Finset.sum_congr rfl
  intro omega _
  rfl



theorem activeBCMean_boundaryClique_eq_wired
    (bdry : V -> Prop) [DecidablePred bdry]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (f : ConfigSpace G.edgeSet -> Real) :
    activeBCMean G (Lattice.boundaryCliqueGraph bdry) (fun _ => p) q f =
      ∑ omega : ConfigSpace (Sym2 V),
        f (restrictActive G omega) * wiredFkProb G bdry p q omega := by
  rw [activeBCMean_eq_bcProb_lift G (Lattice.boundaryCliqueGraph bdry)
    hp hp1 hq]
  exact Finset.sum_congr rfl fun omega _ => by
    rw [bcProb_clique_eq_wiredFkProb]

theorem activeBCProbOf_boundaryClique_eq_wired
    (bdry : V -> Prop) [DecidablePred bdry]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace G.edgeSet)) :
    activeBCProbOf G (Lattice.boundaryCliqueGraph bdry) (fun _ => p) q A =
      ∑ omega : ConfigSpace (Sym2 V),
        (restrictActive G ⁻¹' A).indicator (fun _ => (1 : Real)) omega *
          wiredFkProb G bdry p q omega := by
  rw [activeBCProbOf_eq_bcProb_preimage G (Lattice.boundaryCliqueGraph bdry)
    hp hp1 hq]
  exact Finset.sum_congr rfl fun omega _ => by
    rw [bcProb_clique_eq_wiredFkProb]

end FK
end StatMech
