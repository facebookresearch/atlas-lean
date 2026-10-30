/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoverArmDivergence
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClawDivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedSpanningForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateFarForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutAvoidingRayArm
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedSelfDivergence
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestRooting

/-!
# Rooted arm forests from the arm-adjacency graph

Rooting the arm-adjacency graph of the trifurcations in a box gives a rooted forest of
trifurcations; under arm conditions this yields the bound `Tcount ≤ |∂Λₙ|`.

## i. Overview

Choosing, for each trifurcation, a neighbour closer to a root (`bc38_parentTo`) gives a parent
function and a rank. When the arm-adjacency graph spans every cluster (`bc38_ArmAdjSpanning`) this
is a rooted forest; when it is acyclic the parent is unique. The arm conditions
`bc38_ArmRealisation` and `bc38_ArmCutGeometry` choose, for each trifurcation, an arm end that the
parent cannot reach after the trifurcation is removed. They give parent funnelling, the
self-down-arm property and the count bound. Each condition holds when the box has no trifurcation.

The configuration-wide form of these conditions, for every configuration and every box of radius
`n ≥ 1`, is unsatisfiable when `d ≥ 1`: it implies `Tcount d ω n ≤ boxSV_boundaryCard d n` for every
configuration, which `tfc_not_forall_Tcount_le_boundary` refutes (`bc38_not_forall_residues`,
`bc38_not_forall_spanning_cutGeometry`). The Burton–Keane theorems that assumed them were removed as
vacuous.

## ii. Key results

- `bc38_exists_rootedArmForest` : a rooted arm forest from the spanning condition.
- `bc38_Tcount_le_boundary_of_spanning_cutGeometry` : the trifurcation count bound.

## iii. Table of contents

- A. Closer neighbours and parents
- B. Spanning and acyclic arm adjacency
- C. Arm realisation
- D. Cut geometry
- E. Unsatisfiability of the configuration-wide conditions

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Closer neighbours and parents -/

lemma bc38_exists_closer_neighbour {V : Type*} (G : SimpleGraph V) {root v : V}
    (hr : G.Reachable root v) (hne : v ≠ root) :
    ∃ u, G.Adj v u ∧ G.dist root u < G.dist root v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have hdvpos : 0 < G.dist root v := by
    apply Nat.pos_of_ne_zero
    rw [SimpleGraph.dist_ne_zero_iff_ne_and_reachable]
    exact ⟨hne.symm, hr⟩
  have hpnn : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, hp]; omega
  refine ⟨p.penultimate, (p.adj_penultimate hpnn).symm, ?_⟩
  have hdl : G.dist root p.penultimate ≤ p.dropLast.length := SimpleGraph.dist_le p.dropLast
  rw [SimpleGraph.Walk.length_dropLast, hp] at hdl
  omega

open Classical in
/-- A neighbour of `v` strictly closer to `root v`, or `v` itself when `v` is the root or does not
reach
it. -/
noncomputable def bc38_parentTo {V : Type*} (G : SimpleGraph V) (root : V → V) (v : V) : V :=
  if h : v ≠ root v ∧ G.Reachable (root v) v then
    (bc38_exists_closer_neighbour G h.2 h.1).choose
  else v

lemma bc38_parentTo_spec {V : Type*} (G : SimpleGraph V) (root : V → V) {v : V}
    (hne : v ≠ root v) (hr : G.Reachable (root v) v) :
    G.Adj v (bc38_parentTo G root v) ∧
      G.dist (root v) (bc38_parentTo G root v) < G.dist (root v) v := by
  classical
  have hcond : v ≠ root v ∧ G.Reachable (root v) v := ⟨hne, hr⟩
  unfold bc38_parentTo
  rw [dite_eq_left hcond]
  exact (bc38_exists_closer_neighbour G hr hne).choose_spec

/-! ## B. Spanning and acyclic arm adjacency -/

/-- Connected trifurcations of the box are reachable in the arm-adjacency graph. -/
def bc38_ArmAdjSpanning (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∀ a b : {x : Site d // x ∈ tfc_trifFinset ω n},
    Connected d ω a.1 b.1 → (bc37_armAdjGraph ω n).Reachable a b

lemma bc38_exists_rootedArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hspan : bc38_ArmAdjSpanning ω n) :
    ∃ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧
      (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank x < rank y →
          bc37_ArmAdjacent ω n y (par y) ∧ rank (par y) < rank y) := by
  classical
  set G := bc37_armAdjGraph ω n with hG
  obtain ⟨idx, hidx⟩ := (inferInstance : Countable (Site d)).exists_injective_nat
  set root : {x : Site d // x ∈ tfc_trifFinset ω n} → {x : Site d // x ∈ tfc_trifFinset ω n} :=
    fun v => (G.connectedComponentMk v).nonempty_supp.some with hroot
  have hrr : ∀ v, G.Reachable (root v) v := by
    intro v; rw [← SimpleGraph.ConnectedComponent.eq]
    exact (G.connectedComponentMk v).nonempty_supp.some_mem
  have hroot_inv : ∀ v w, G.Reachable v w → root v = root w := by
    intro v w hvw
    have : G.connectedComponentMk v = G.connectedComponentMk w :=
      SimpleGraph.ConnectedComponent.eq.mpr hvw
    simp only [hroot, this]
  set dep : Site d → ℕ := fun v =>
    if hv : v ∈ tfc_trifFinset ω n then G.dist (root ⟨v, hv⟩) ⟨v, hv⟩ else 0 with hdep
  set par : Site d → Site d := fun v =>
    if hv : v ∈ tfc_trifFinset ω n then (bc38_parentTo G root ⟨v, hv⟩).1 else v with hpar
  have hdep0 : ∀ (v : Site d) (hv : v ∈ tfc_trifFinset ω n),
      dep v = 0 ↔ (⟨v, hv⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) = root ⟨v, hv⟩ := by
    intro v hv
    simp only [hdep, dite_eq_left hv]
    rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable]
    constructor
    · rintro (h | h); · exact h.symm
      · exact absurd (hrr ⟨v, hv⟩) h
    · intro h; exact Or.inl h.symm
  refine ⟨fun v => toLex (dep v, idx v), par, ?_, ?_⟩
  · intro x _hxbox _htri y _hybox _htriy hxy _hconn hrankeq
    have hidxeq : idx x = idx y := by simpa using congrArg (fun p => (ofLex p).2) hrankeq
    exact hxy (hidx hidxeq)
  · intro x hxbox htri y hybox htriy hxy hconn hlt
    have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
    simp only at hlt
    have hxyreach : G.Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ := hspan ⟨x, hxT⟩ ⟨y, hyT⟩ hconn
    have hrootxy : root ⟨x, hxT⟩ = root ⟨y, hyT⟩ := hroot_inv _ _ hxyreach
    have hynonroot : (⟨y, hyT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) ≠ root ⟨y, hyT⟩ := by
      intro hyroot
      have hdepy0 : dep y = 0 := (hdep0 y hyT).mpr hyroot
      rw [hdepy0, Prod.Lex.toLex_lt_toLex] at hlt
      have hdepx0 : dep x = 0 := by rcases hlt with h | ⟨h, _⟩; · omega
                                    · exact h
      have hxroot : (⟨x, hxT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) = root ⟨x, hxT⟩ :=
        (hdep0 x hxT).mp hdepx0
      apply hxy
      have hxy_eq : (⟨x, hxT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) = ⟨y, hyT⟩ := by
        rw [hxroot, hrootxy, ← hyroot]
      exact congrArg Subtype.val hxy_eq
    obtain ⟨hadj, hdlt⟩ := bc38_parentTo_spec G root hynonroot (hrr ⟨y, hyT⟩)
    have hpary : par y = (bc38_parentTo G root ⟨y, hyT⟩).1 := by simp only [hpar, dite_eq_left hyT]
    have hparyT : par y ∈ tfc_trifFinset ω n := by
      rw [hpary]; exact (bc38_parentTo G root ⟨y, hyT⟩).2
    have hpar_pack : (⟨par y, hparyT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n})
        = bc38_parentTo G root ⟨y, hyT⟩ := Subtype.ext hpary
    refine ⟨?_, ?_⟩
    · have : G.Adj ⟨y, hyT⟩ ⟨par y, hparyT⟩ := by rw [hpar_pack]; exact hadj
      exact this
    · have hyparreach : G.Reachable ⟨y, hyT⟩ (bc38_parentTo G root ⟨y, hyT⟩) := hadj.reachable
      have hrootpary : root (bc38_parentTo G root ⟨y, hyT⟩) = root ⟨y, hyT⟩ :=
        hroot_inv _ _ hyparreach.symm
      have hdeppary : dep (par y) = G.dist (root ⟨y, hyT⟩) (bc38_parentTo G root ⟨y, hyT⟩) := by
        simp only [hdep, dite_eq_left hparyT]
        rw [hpar_pack, hrootpary]
      have hdepy : dep y = G.dist (root ⟨y, hyT⟩) ⟨y, hyT⟩ := by simp only [hdep, dite_eq_left hyT]
      have hdeplt : dep (par y) < dep y := by rw [hdeppary, hdepy]; exact hdlt
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hdeplt)

/-- The arm-adjacency graph of the box is acyclic. -/
def bc38_ArmAdjAcyclic (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  (bc37_armAdjGraph ω n).IsAcyclic

lemma bc38_armAdjAcyclic_iff_path_unique (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc38_ArmAdjAcyclic ω n ↔
      ∀ ⦃a b⦄ (p q : (bc37_armAdjGraph ω n).Path a b), p = q :=
  SimpleGraph.isAcyclic_iff_subsingleton_path.trans
    ⟨fun h a b p q => (h a b).elim p q, fun h _a _b => ⟨fun p q => h p q⟩⟩

set_option linter.unusedDecidableInType false in
lemma bc38_unique_closer_neighbour_of_acyclic {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hac : G.IsAcyclic) {root v u₁ u₂ : V} (h1 : G.Adj v u₁) (h2 : G.Adj v u₂)
    (hd1 : G.dist root u₁ < G.dist root v) (hd2 : G.dist root u₂ < G.dist root v) :
    u₁ = u₂ := by
  have hvr : G.Reachable root v := SimpleGraph.Reachable.of_dist_ne_zero (by omega)
  obtain ⟨p1, hpp1, hlp1⟩ := (hvr.trans h1.reachable).exists_path_of_dist
  obtain ⟨p2, hpp2, hlp2⟩ := (hvr.trans h2.reachable).exists_path_of_dist
  have hv1 : v ∉ p1.support := fun hv => by
    have hle : G.dist root v ≤ (p1.takeUntil v hv).length := SimpleGraph.dist_le _
    have := p1.length_takeUntil_le_length hv; omega
  have hv2 : v ∉ p2.support := fun hv => by
    have hle : G.dist root v ≤ (p2.takeUntil v hv).length := SimpleGraph.dist_le _
    have := p2.length_takeUntil_le_length hv; omega
  have heq : (⟨p1.concat h1.symm, hpp1.concat hv1 h1.symm⟩ : G.Path root v)
      = ⟨p2.concat h2.symm, hpp2.concat hv2 h2.symm⟩ :=
    (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hac _ _).elim _ _
  have heqw : p1.concat h1.symm = p2.concat h2.symm := Subtype.mk.inj heq
  calc u₁ = (p1.concat h1.symm).penultimate := by simp [SimpleGraph.Walk.penultimate_concat]
    _ = (p2.concat h2.symm).penultimate := by rw [heqw]
    _ = u₂ := by simp [SimpleGraph.Walk.penultimate_concat]

lemma bc38_unique_armParent (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hac : bc38_ArmAdjAcyclic ω n)
    {root v u₁ u₂ : {x : Site d // x ∈ tfc_trifFinset ω n}}
    (h1 : (bc37_armAdjGraph ω n).Adj v u₁) (h2 : (bc37_armAdjGraph ω n).Adj v u₂)
    (hd1 : (bc37_armAdjGraph ω n).dist root u₁ < (bc37_armAdjGraph ω n).dist root v)
    (hd2 : (bc37_armAdjGraph ω n).dist root u₂ < (bc37_armAdjGraph ω n).dist root v) :
    u₁ = u₂ :=
  bc38_unique_closer_neighbour_of_acyclic (bc37_armAdjGraph ω n) hac h1 h2 hd1 hd2

/-! ## C. Arm realisation -/

/-- Arm realisation: for every rank and parent function separating connected trifurcations, arm ends
exist that the parent cannot reach after the trifurcation is removed, while lower trifurcations
still reach them. -/
def bc38_ArmRealisation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
        bc37_ArmAdjacent ω n y (par y) ∧ rank (par y) < rank y) →
    ∃ b : Site d → Site d,
      (∀ x, x ∈ box d n → IsTrifurcation d ω x →
        b x ∈ box d n ∧ Connected d ω x (b x) ∧
        (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
      (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank x < rank y →
          (¬ Connected d (removeSite y ω) (b y) (b (par y))) ∧
          (¬ Connected d (removeSite y ω) (b y) (par y)) ∧
          (x ≠ par y → Connected d (removeSite y ω) (b x) (par y)))

lemma bc38_parentFunneling_of_residues (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hspan : bc38_ArmAdjSpanning ω n) (hreal : bc38_ArmRealisation ω n) :
    bc37_ParentFunneling ω n := by
  obtain ⟨rank, par, hinj, hroot⟩ := bc38_exists_rootedArmForest ω n hspan
  obtain ⟨b, hdata, hclauses⟩ := hreal rank par hroot
  exact ⟨b, rank, par, hdata, hinj, hclauses⟩

lemma bc38_selfDownArm_of_residues (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hspan : bc38_ArmAdjSpanning ω n) (hreal : bc38_ArmRealisation ω n) :
    bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n (bc38_parentFunneling_of_residues ω n hspan hreal)

lemma bc38_Tcount_le_boundary_of_residues (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hspan : bc38_ArmAdjSpanning ω n) (hreal : bc38_ArmRealisation ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn (bc38_selfDownArm_of_residues ω n hspan hreal)

lemma bc38_armAdjSpanning_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc38_ArmAdjSpanning ω n := by
  intro a _b _hconn
  exact absurd (tfc_mem_trifFinset.mp a.2).2 (hno a.1 (tfc_mem_trifFinset.mp a.2).1)

set_option linter.unusedVariables false in
lemma bc38_armAdjSpanning_of_threePath (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ tfc_trifFinset ω n → x = x₀ ∨ x = m ∨ x = g)
    (hx0T : x₀ ∈ tfc_trifFinset ω n) (hmT : m ∈ tfc_trifFinset ω n) (hgT : g ∈ tfc_trifFinset ω n)
    (hadj_x0m : bc37_ArmAdjacent ω n x₀ m) (hadj_mg : bc37_ArmAdjacent ω n m g) :
    bc38_ArmAdjSpanning ω n := by
  classical
  set G := bc37_armAdjGraph ω n with hG
  have exm : G.Adj ⟨x₀, hx0T⟩ ⟨m, hmT⟩ := hadj_x0m
  have emg : G.Adj ⟨m, hmT⟩ ⟨g, hgT⟩ := hadj_mg
  have rx0m : G.Reachable ⟨x₀, hx0T⟩ ⟨m, hmT⟩ := exm.reachable
  have rmg : G.Reachable ⟨m, hmT⟩ ⟨g, hgT⟩ := emg.reachable
  have rx0g : G.Reachable ⟨x₀, hx0T⟩ ⟨g, hgT⟩ := rx0m.trans rmg
  have hbase : ∀ (v : {x : Site d // x ∈ tfc_trifFinset ω n}), G.Reachable ⟨x₀, hx0T⟩ v := by
    intro v
    rcases hthree v.1 v.2 with h | h | h
    · rw [show v = ⟨x₀, hx0T⟩ from Subtype.ext h]
    · rw [show v = ⟨m, hmT⟩ from Subtype.ext h]; exact rx0m
    · rw [show v = ⟨g, hgT⟩ from Subtype.ext h]; exact rx0g
  intro a b _hconn
  exact (hbase a).symm.trans (hbase b)

/-! ## D. Cut geometry -/

/-- Arm cut geometry: arm ends `b x` in the box with infinite clusters after removing `x`, which no
other site reaches after `x` is removed. -/
def bc38_ArmCutGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ t s, t ∈ box d n → IsTrifurcation d ω t → bc37_ArmAdjacent ω n t s →
      (¬ Connected d (removeSite t ω) (b t) (b s)) ∧
      (¬ Connected d (removeSite t ω) (b t) s) ∧
      (∀ x, x ≠ s → Connected d (removeSite t ω) (b x) s))

lemma bc38_armRealisation_of_cutGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc38_ArmCutGeometry ω n) : bc38_ArmRealisation ω n := by
  obtain ⟨b, hdata, hclauses⟩ := hgeo
  intro rank par hroot
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hpadj, _hprank⟩ := hroot x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hloc, hself, hfun⟩ := hclauses y (par y) hybox htriy hpadj
  exact ⟨hloc, hself, fun hxne => hfun x hxne⟩

lemma bc38_armCutGeometry_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc38_ArmCutGeometry ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro t s htbox htri _; exact absurd htri (hno t htbox)

lemma bc38_armRealisation_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc38_ArmRealisation ω n :=
  bc38_armRealisation_of_cutGeometry ω n (bc38_armCutGeometry_of_noTrif ω n hno)

lemma bc38_cutGeometry_shadow_consistent (parNode bpar bself : ℕ)
    (hnode : parNode ≠ bself) (hbpar : bpar ≠ bself) :
    ∃ up : ℕ → Prop,
      (¬ up bself ∧ up bpar) ∧
      (¬ up bself ∧ up parNode) ∧
      (∀ w, w ≠ parNode → w ≠ bself → up parNode ∧ up w) := by
  refine ⟨fun w => w ≠ bself, ⟨by simp, hbpar⟩, ⟨by simp, hnode⟩, ?_⟩
  intro w _hwn hwb
  exact ⟨hnode, hwb⟩

lemma bc38_parentFunneling_of_spanning_cutGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hspan : bc38_ArmAdjSpanning ω n) (hgeo : bc38_ArmCutGeometry ω n) :
    bc37_ParentFunneling ω n :=
  bc38_parentFunneling_of_residues ω n hspan (bc38_armRealisation_of_cutGeometry ω n hgeo)

lemma bc38_selfDownArm_of_spanning_cutGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hspan : bc38_ArmAdjSpanning ω n) (hgeo : bc38_ArmCutGeometry ω n) :
    bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n
    (bc38_parentFunneling_of_spanning_cutGeometry ω n hspan hgeo)

lemma bc38_Tcount_le_boundary_of_spanning_cutGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hspan : bc38_ArmAdjSpanning ω n) (hgeo : bc38_ArmCutGeometry ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn
    (bc38_selfDownArm_of_spanning_cutGeometry ω n hspan hgeo)

/-! ## E. Unsatisfiability of the configuration-wide conditions -/

/-- `bc38_ArmAdjSpanning` and `bc38_ArmRealisation` for every configuration and every box of radius
`n ≥ 1` are impossible when `d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`,
which `tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma bc38_not_forall_residues (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc38_ArmAdjSpanning ω n ∧ bc38_ArmRealisation ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bc38_Tcount_le_boundary_of_residues ω n hn (h ω n hn).1 (h ω n hn).2

/-- `bc38_ArmAdjSpanning` and `bc38_ArmCutGeometry` for every configuration and every box of radius
`n ≥ 1` are impossible when `d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`,
which `tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma bc38_not_forall_spanning_cutGeometry (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc38_ArmAdjSpanning ω n ∧ bc38_ArmCutGeometry ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bc38_Tcount_le_boundary_of_spanning_cutGeometry ω n hn (h ω n hn).1 (h ω n hn).2

end StatMech.Walls
