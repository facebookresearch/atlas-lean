/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABFiniteGraph
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual

/-!
# Graph automorphisms and the finite-volume percolation magnetization

Graph automorphisms preserving the couplings preserve the percolation probabilities with a ghost
field; on vertex-transitive graphs all sites have the same magnetization.

## i. Overview

An automorphism `σ` of `G` extends to the ghost graph fixing the ghost and acts on configurations.
Inhomogeneous product measures transform covariantly, and connection events are mapped to connection
events. Hence `P(σ(o) ↔ ghost) = P(o ↔ ghost)`, and on transitive graphs the Aizenman–Barsky
inequality holds with constant equal to the common row sum.

## ii. Key results

- `abfs_probV_transfer` : transfer of probabilities under a relabelling
- `abfsEdgeEquiv` : the action on ghost-graph edges
- `abfs_mag_eq_of_automorphism` : invariance of the magnetization
- `abfs_aizenmanBarsky_of_transitive` : the inequality on transitive graphs

## iii. Table of contents

- A. Relabelling product measures
- B. Automorphisms of the ghost graph
- C. Invariance of the magnetization

## iv. References

- M. Aizenman, D. J. Barsky, "Sharpness of the phase transition in percolation models", Comm. Math.
  Phys. 108 (1987) 489–526

-/

@[expose] public section

open Finset Set SimpleGraph

namespace StatMech
namespace Sharpness

open ConfigSpace RandomCurrent

variable {E F : Type*} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

/-! ## A. Relabelling product measures -/

/-- The edge law `b ↦ p_e` (open) or `1 - p_e` (closed). -/
private noncomputable def abfsLaw (p : E -> Real) (e : E) (b : Bool) : Real :=
  if b then p e else 1 - p e

private lemma abfs_probV_eq_wprob (p : E -> Real) (A : Set (ConfigSpace E)) :
    probV p A = wprob (abfsLaw p) A := by
  unfold probV wprob configWeightV pweight edgeWeightV abfsLaw
  rfl

lemma abfs_probV_transfer (e : E ≃ F) (p : E -> Real)
    (A : Set (ConfigSpace E)) :
    probV p A =
      probV (fun y => p (e.symm y)) ((cfgEquiv e) ⁻¹' A) := by
  rw [abfs_probV_eq_wprob, abfs_probV_eq_wprob]
  exact wprob_transfer e (abfsLaw p) A

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## B. Automorphisms of the ghost graph -/

/-- The extension of a vertex permutation to the ghost graph fixing the ghost. -/
def abfsOptionEquiv (sigma : V ≃ V) : Option V ≃ Option V := sigma.optionCongr

/-- The induced permutation of unordered pairs of the ghost graph. -/
def abfsEdgeEquiv (sigma : V ≃ V) :
    Sym2 (Option V) ≃ Sym2 (Option V) :=
  StatMech.Lattice.sym2Congr (abfsOptionEquiv sigma)

omit [Fintype V] [DecidableEq V] in
@[simp] lemma abfsOptionEquiv_some (sigma : V ≃ V) (x : V) :
    abfsOptionEquiv sigma (some x) = some (sigma x) := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] lemma abfsOptionEquiv_none (sigma : V ≃ V) :
    abfsOptionEquiv sigma none = none := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] lemma abfsEdgeEquiv_mk (sigma : V ≃ V) (a b : Option V) :
    abfsEdgeEquiv sigma s(a, b) =
      s(abfsOptionEquiv sigma a, abfsOptionEquiv sigma b) := by
  simp [abfsEdgeEquiv, StatMech.Lattice.sym2Congr]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma abfs_openSub_adj_relabel (sigma : V ≃ V)
    (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y)
    (omega : ConfigSpace (Sym2 (Option V))) (a b : Option V) :
    (openSub (withGhost G) (cfgEquiv (abfsEdgeEquiv sigma) omega)).Adj a b <->
      (openSub (withGhost G) omega).Adj
        (abfsOptionEquiv sigma a) (abfsOptionEquiv sigma b) := by
  rcases a with _ | x <;> rcases b with _ | y
  · simp [openSub, withGhost]
  · simp [openSub, withGhost, abfsEdgeEquiv]
  · simp [openSub, withGhost, abfsEdgeEquiv]
  · simp only [openSub, withGhost, cfgEquiv_apply, abfsEdgeEquiv_mk,
      abfsOptionEquiv_some, and_congr_left_iff]
    exact fun _ => (hG x y).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma abfs_connWithin_univ_relabel (sigma : V ≃ V)
    (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y)
    (omega : ConfigSpace (Sym2 (Option V))) (a b : Option V) :
    ConnWithin (withGhost G) (cfgEquiv (abfsEdgeEquiv sigma) omega) Set.univ
        ⟨a, Set.mem_univ _⟩ ⟨b, Set.mem_univ _⟩ <->
      ConnWithin (withGhost G) omega Set.univ
        ⟨abfsOptionEquiv sigma a, Set.mem_univ _⟩
        ⟨abfsOptionEquiv sigma b, Set.mem_univ _⟩ := by
  constructor
  · intro h
    let f :
        ((openSub (withGhost G)
          (cfgEquiv (abfsEdgeEquiv sigma) omega)).induce Set.univ) →g
        ((openSub (withGhost G) omega).induce Set.univ) :=
      { toFun := fun z => ⟨abfsOptionEquiv sigma z, Set.mem_univ _⟩
        map_rel' := fun {x y} hxy =>
          (abfs_openSub_adj_relabel G sigma hG omega x y).mp hxy }
    exact h.map f
  · intro h
    let f :
        ((openSub (withGhost G) omega).induce Set.univ) →g
        ((openSub (withGhost G)
          (cfgEquiv (abfsEdgeEquiv sigma) omega)).induce Set.univ) :=
      { toFun := fun z => ⟨(abfsOptionEquiv sigma).symm z, Set.mem_univ _⟩
        map_rel' := fun {x y} hxy => by
          apply (abfs_openSub_adj_relabel G sigma hG omega
            ((abfsOptionEquiv sigma).symm x)
            ((abfsOptionEquiv sigma).symm y)).mpr
          simpa using hxy }
    have e : ∀ c, f ⟨abfsOptionEquiv sigma c, Set.mem_univ _⟩ = ⟨c, Set.mem_univ _⟩ :=
      fun c => Subtype.ext ((abfsOptionEquiv sigma).symm_apply_apply c)
    have hm := h.map f
    rw [e, e] at hm
    exact hm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma abfs_preimage_connEvent (sigma : V ≃ V)
    (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y) (o : V) :
    (cfgEquiv (abfsEdgeEquiv sigma)) ⁻¹'
        connEvent (withGhost G) Set.univ (some o) {none} =
      connEvent (withGhost G) Set.univ (some (sigma o)) {none} := by
  ext omega
  change ConnToSet (withGhost G) (cfgEquiv (abfsEdgeEquiv sigma) omega)
      Set.univ (some o) {none} <->
    ConnToSet (withGhost G) omega Set.univ (some (sigma o)) {none}
  constructor
  · rintro ⟨_, b, _, hb, hconn⟩
    have hbnone : b = none := Set.mem_singleton_iff.mp hb
    subst b
    exact ⟨Set.mem_univ _, none, Set.mem_univ _, rfl,
      (abfs_connWithin_univ_relabel G sigma hG omega (some o) none).mp hconn⟩
  · rintro ⟨_, b, _, hb, hconn⟩
    have hbnone : b = none := Set.mem_singleton_iff.mp hb
    subst b
    exact ⟨Set.mem_univ _, none, Set.mem_univ _, rfl,
      (abfs_connWithin_univ_relabel G sigma hG omega (some o) none).mpr hconn⟩

/-! ## C. Invariance of the magnetization -/

lemma abfs_params_invariant (J : Sym2 V -> Real) (beta h : Real)
    (sigma : V ≃ V)
    (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y)
    (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y))
    (e : Sym2 (Option V)) :
    abfaParams G J beta h (abfsEdgeEquiv sigma e) =
      abfaParams G J beta h e := by
  induction e using Sym2.ind with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp [abfsEdgeEquiv, abfaParams, abpdBetaFieldParams, paramOn,
          FieldGhostDict.ghostEdges, abfaLiftCoupling,
          FieldGhostDict.ghostCoupling]
      · simp [abfsEdgeEquiv, abfaParams, abpdBetaFieldParams, paramOn,
          FieldGhostDict.ghostEdges]
      · simp [abfsEdgeEquiv, abfaParams, abpdBetaFieldParams, paramOn,
          FieldGhostDict.ghostEdges, Sym2.eq_swap]
      · simp only [abfsEdgeEquiv_mk, abfsOptionEquiv_some, abfaParams,
          abpdBetaFieldParams, paramOn]
        have hedge : s(sigma x, sigma y) ∈ G.edgeFinset <->
            s(x, y) ∈ G.edgeFinset := by
          simp only [mem_edgeFinset]
          exact hG x y
        have hg1 : s(some (sigma x), some (sigma y)) ∉
            FieldGhostDict.ghostEdges V := by
          simp [FieldGhostDict.ghostEdges]
        have hg2 : s(some x, some y) ∉ FieldGhostDict.ghostEdges V := by
          simp [FieldGhostDict.ghostEdges]
        simp only [hg1, hg2, ite_false, abfaLiftCoupling_some_some]
        apply congrArg (fun z => pBeta z beta)
        by_cases he : s(x, y) ∈ G.edgeFinset
        · have he' : s(sigma x, sigma y) ∈ G.edgeFinset := hedge.mpr he
          simp [he, he', hJ x y]
        · have he' : s(sigma x, sigma y) ∉ G.edgeFinset :=
            fun hmem => he (hedge.mp hmem)
          simp [he, he']

lemma abfs_mag_eq_of_automorphism (J : Sym2 V -> Real) (o : V)
    (beta h : Real) (sigma : V ≃ V)
    (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y)
    (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y)) :
    probV (abfaParams G J beta h)
        (connEvent (withGhost G) Set.univ (some (sigma o)) {none}) =
      abfaMag G J o beta h := by
  unfold abfaMag
  symm
  rw [abfs_probV_transfer (abfsEdgeEquiv sigma)]
  have hp : (fun e => abfaParams G J beta h
      ((abfsEdgeEquiv sigma).symm e)) = abfaParams G J beta h := by
    funext e
    rw [← abfs_params_invariant G J beta h sigma hG hJ
      ((abfsEdgeEquiv sigma).symm e)]
    simp
  rw [hp, abfs_preimage_connEvent G sigma hG o]

lemma abfs_aizenmanBarsky_of_transitive (J : Sym2 V -> Real) (o : V)
    (beta h J0 : Real)
    (hJnonneg : ∀ e ∈ G.edgeFinset, 0 <= J e)
    (hrow : forall x, abcrIncidentCoupling G J x = J0)
    (hbeta : 0 <= beta) (hh : 0 <= h)
    (move : V -> (V ≃ V))
    (hmove : forall x, move x o = x)
    (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
    (hJ : forall x u v, J s(move x u, move x v) = J s(u, v)) :
    deriv (fun b => abfaMag G J o b h) beta <=
      J0 * abfaMag G J o beta h * deriv (fun t => abfaMag G J o beta t) h := by
  apply abfa_aizenmanBarsky G J o beta h J0 hJnonneg hrow hbeta hh
  intro x
  rw [← hmove x]
  exact abfs_mag_eq_of_automorphism G J o beta h (move x) (hG x) (hJ x)

end Sharpness
end StatMech
