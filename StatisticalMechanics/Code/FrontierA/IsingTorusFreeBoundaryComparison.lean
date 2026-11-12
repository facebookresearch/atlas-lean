/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingTorusEmbedding
import Code.Ising.GinibreBoundary
import Code.Ising.GHSVertexPartition
import Code.Sharpness.HighTempPlusBox
import Code.FrontierB.InhomogeneousFiniteVolumeRelabel











open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]




def finiteCutBoundaryField (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool) (x : {v : V // v ∈ S}) : Real :=
  ∑ y : {v : V // v ∉ S}, if G.Adj x.1 y.1 then spin outside y else 0


def finiteCutPlusBoundaryField (S : Finset V)
    (x : {v : V // v ∈ S}) : Real :=
  ∑ y : {v : V // v ∉ S}, if G.Adj x.1 y.1 then 1 else 0

theorem finiteCutPlusBoundaryField_nonneg (S : Finset V)
    (x : {v : V // v ∈ S}) :
    0 ≤ finiteCutPlusBoundaryField G S x := by
  unfold finiteCutPlusBoundaryField
  positivity



theorem abs_finiteCutBoundaryField_le_plus (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool) (x : {v : V // v ∈ S}) :
    |finiteCutBoundaryField G S outside x| ≤
      finiteCutPlusBoundaryField G S x := by
  unfold finiteCutBoundaryField finiteCutPlusBoundaryField
  calc
    |∑ y : {v : V // v ∉ S},
        if G.Adj x.1 y.1 then spin outside y else 0| ≤
        ∑ y : {v : V // v ∉ S},
          |if G.Adj x.1 y.1 then spin outside y else 0| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ y : {v : V // v ∉ S},
        if G.Adj x.1 y.1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hxy : G.Adj x.1 y.1
      · simp only [if_pos hxy]
        unfold spin
        split <;> norm_num
      · simp [hxy]


def finiteCutMerge (S : Finset V) (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) : ConfigSpace V :=
  ghsvp_mergeConfig S inside outside

@[simp] theorem finiteCutMerge_inside (S : Finset V)
    (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) (x : {v : V // v ∈ S}) :
    finiteCutMerge S inside outside x.1 = inside x := by
  simp [finiteCutMerge, ghsvp_mergeConfig, x.2]

@[simp] theorem finiteCutMerge_outside (S : Finset V)
    (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) (x : {v : V // v ∉ S}) :
    finiteCutMerge S inside outside x.1 = outside x := by
  simp [finiteCutMerge, ghsvp_mergeConfig, x.2]

@[simp] theorem spin_finiteCutMerge_inside (S : Finset V)
    (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) (x : {v : V // v ∈ S}) :
    spin (finiteCutMerge S inside outside) x.1 = spin inside x := by
  unfold spin
  rw [finiteCutMerge_inside]

@[simp] theorem spin_finiteCutMerge_outside (S : Finset V)
    (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) (x : {v : V // v ∉ S}) :
    spin (finiteCutMerge S inside outside) x.1 = spin outside x := by
  unfold spin
  rw [finiteCutMerge_outside]


def finiteCutInternalEdges (S : Finset V) : Finset (Sym2 V) :=
  ghsvp_vertexEdges G.edgeFinset S


def finiteCutExteriorEdges (S : Finset V) : Finset (Sym2 V) :=
  ghsvp_vertexEdges G.edgeFinset (Finset.univ \ S)


def finiteCutCrossEdges (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset \ (finiteCutInternalEdges G S ∪ finiteCutExteriorEdges G S)

@[simp] theorem mk_mem_finiteCutInternalEdges_iff (S : Finset V) (x y : V) :
    s(x, y) ∈ finiteCutInternalEdges G S ↔
      G.Adj x y ∧ x ∈ S ∧ y ∈ S := by
  simp [finiteCutInternalEdges, ghsvp_vertexEdges, Sharpness.edgeInside,
    SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]

@[simp] theorem mk_mem_finiteCutExteriorEdges_iff (S : Finset V) (x y : V) :
    s(x, y) ∈ finiteCutExteriorEdges G S ↔
      G.Adj x y ∧ x ∉ S ∧ y ∉ S := by
  simp [finiteCutExteriorEdges, ghsvp_vertexEdges, Sharpness.edgeInside,
    SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]

@[simp] theorem mk_mem_finiteCutCrossEdges_iff (S : Finset V) (x y : V) :
    s(x, y) ∈ finiteCutCrossEdges G S ↔
      G.Adj x y ∧ ((x ∈ S ∧ y ∉ S) ∨ (x ∉ S ∧ y ∈ S)) := by
  simp only [finiteCutCrossEdges, Finset.mem_sdiff, Finset.mem_union,
    mk_mem_finiteCutInternalEdges_iff, mk_mem_finiteCutExteriorEdges_iff,
    SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨hxy, hnot⟩
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · exact (hnot (Or.inl ⟨hxy, hx, hy⟩)).elim
    · exact ⟨hxy, Or.inl ⟨hx, hy⟩⟩
    · exact ⟨hxy, Or.inr ⟨hx, hy⟩⟩
    · exact (hnot (Or.inr ⟨hxy, hx, hy⟩)).elim
  · rintro ⟨hxy, hcross⟩
    refine ⟨hxy, ?_⟩
    rcases hcross with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rintro (⟨_, _, hy'⟩ | ⟨_, hx', _⟩)
      · exact hy hy'
      · exact hx' hx
    · rintro (⟨_, hx', _⟩ | ⟨_, _, hy'⟩)
      · exact hx hx'
      · exact hy' hy



def finiteCutCrossPairs (S : Finset V) :
    Finset ({v : V // v ∈ S} × {v : V // v ∉ S}) :=
  (Finset.univ ×ˢ Finset.univ).filter fun p => G.Adj p.1.1 p.2.1


theorem sum_cross_bond_finiteCutMerge_eq_boundaryField
    (S : Finset V) (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) :
    (∑ e ∈ finiteCutCrossEdges G S, bond (finiteCutMerge S inside outside) e) =
      ∑ x : {v : V // v ∈ S},
        finiteCutBoundaryField G S outside x * spin inside x := by
  unfold finiteCutBoundaryField
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [ite_mul, zero_mul]
  let P := finiteCutCrossPairs G S
  have hpairs : (∑ y : {v : V // v ∉ S},
      ∑ x : {v : V // v ∈ S},
        if G.Adj x.1 y.1 then spin outside y * spin inside x else 0) =
      ∑ p ∈ P, spin outside p.2 * spin inside p.1 := by
    rw [Finset.sum_comm]
    simp only [P, finiteCutCrossPairs, Finset.sum_filter]
    rw [Finset.sum_product]
  rw [hpairs]
  symm
  apply Finset.sum_bij
      (fun p _ => s(p.1.1, p.2.1))
  · intro p hp
    simp only [P, finiteCutCrossPairs, Finset.mem_filter,
      Finset.mem_product, Finset.mem_univ, true_and] at hp
    exact (mk_mem_finiteCutCrossEdges_iff G S p.1.1 p.2.1).2
      ⟨hp, Or.inl ⟨p.1.2, p.2.2⟩⟩
  · intro p hp q hq hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with hpq | hpq
    · exact Prod.ext (Subtype.ext hpq.1) (Subtype.ext hpq.2)
    · exact (q.2.2 (hpq.1 ▸ p.1.2)).elim
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mk_mem_finiteCutCrossEdges_iff] at he
      rcases he.2 with hxy | hxy
      · let p : {v : V // v ∈ S} × {v : V // v ∉ S} :=
          (⟨x, hxy.1⟩, ⟨y, hxy.2⟩)
        refine ⟨p, ?_, rfl⟩
        simp [P, finiteCutCrossPairs, p, he.1]
      · let p : {v : V // v ∈ S} × {v : V // v ∉ S} :=
          (⟨y, hxy.2⟩, ⟨x, hxy.1⟩)
        refine ⟨p, ?_, Sym2.eq_swap⟩
        simp [P, finiteCutCrossPairs, p, he.1.symm]
  · intro p hp
    rw [bond_mk, spin_finiteCutMerge_inside, spin_finiteCutMerge_outside]
    ring


def finiteCutGraph (S : Finset V) : SimpleGraph {v : V // v ∈ S} :=
  G.comap Subtype.val

instance finiteCutGraph_decidableRel (S : Finset V) :
    DecidableRel (finiteCutGraph G S).Adj := fun x y => inferInstanceAs
      (Decidable (G.Adj x.1 y.1))


theorem sum_internal_bond_finiteCutMerge_eq_cutGraph
    (S : Finset V) (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) :
    (∑ e ∈ finiteCutInternalEdges G S,
        bond (finiteCutMerge S inside outside) e) =
      ∑ e ∈ (finiteCutGraph G S).edgeFinset, bond inside e := by
  symm
  apply Finset.sum_bij
      (fun e _ => Sym2.map (Subtype.val : {v : V // v ∈ S} → V) e)
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [Sym2.map_mk]
      exact (mk_mem_finiteCutInternalEdges_iff G S x.1 y.1).2
        ⟨by simpa [finiteCutGraph] using he, x.2, y.2⟩
  · intro e he f hf hef
    exact Sym2.map.injective Subtype.val_injective hef
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mk_mem_finiteCutInternalEdges_iff] at he
      let e' : Sym2 {v : V // v ∈ S} :=
        s((⟨x, he.2.1⟩ : {v : V // v ∈ S}), ⟨y, he.2.2⟩)
      refine ⟨e', ?_, ?_⟩
      · simpa [e', finiteCutGraph] using he.1
      · simp [e']
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [Sym2.map_mk, bond_mk, bond_mk,
        spin_finiteCutMerge_inside, spin_finiteCutMerge_inside]

theorem finiteCutInternalEdges_subset (S : Finset V) :
    finiteCutInternalEdges G S ⊆ G.edgeFinset := by
  intro e he
  exact (Finset.mem_filter.1 he).1

theorem finiteCutExteriorEdges_subset (S : Finset V) :
    finiteCutExteriorEdges G S ⊆ G.edgeFinset := by
  intro e he
  exact (Finset.mem_filter.1 he).1

theorem finiteCutInternalEdges_disjoint_exterior (S : Finset V) :
    Disjoint (finiteCutInternalEdges G S) (finiteCutExteriorEdges G S) := by
  rw [Finset.disjoint_left]
  intro e hi he
  induction e using Sym2.ind with
  | _ x y =>
    have hi' := (mk_mem_finiteCutInternalEdges_iff G S x y).1 hi
    have he' := (mk_mem_finiteCutExteriorEdges_iff G S x y).1 he
    exact he'.2.1 hi'.2.1



theorem sum_bond_eq_internal_add_cross_add_exterior
    (S : Finset V) (sigma : ConfigSpace V) :
    (∑ e ∈ G.edgeFinset, bond sigma e) =
      (∑ e ∈ finiteCutInternalEdges G S, bond sigma e) +
      (∑ e ∈ finiteCutCrossEdges G S, bond sigma e) +
      ∑ e ∈ finiteCutExteriorEdges G S, bond sigma e := by
  let U := finiteCutInternalEdges G S ∪ finiteCutExteriorEdges G S
  have hU : U ⊆ G.edgeFinset := by
    exact Finset.union_subset
      (finiteCutInternalEdges_subset G S)
      (finiteCutExteriorEdges_subset G S)
  have hsplit :
      (∑ e ∈ G.edgeFinset \ U, bond sigma e) +
          ∑ e ∈ U, bond sigma e =
        ∑ e ∈ G.edgeFinset, bond sigma e :=
    Finset.sum_sdiff hU
  have hcross : G.edgeFinset \ U = finiteCutCrossEdges G S := by
    rfl
  have hunion : (∑ e ∈ U, bond sigma e) =
      (∑ e ∈ finiteCutInternalEdges G S, bond sigma e) +
        ∑ e ∈ finiteCutExteriorEdges G S, bond sigma e := by
    exact Finset.sum_union (finiteCutInternalEdges_disjoint_exterior G S)
  rw [hcross, hunion] at hsplit
  linarith


theorem sum_exterior_bond_finiteCutMerge_eq
    (S : Finset V) (inside inside' : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) :
    (∑ e ∈ finiteCutExteriorEdges G S,
        bond (finiteCutMerge S inside outside) e) =
      ∑ e ∈ finiteCutExteriorEdges G S,
        bond (finiteCutMerge S inside' outside) e := by
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    have he' := (mk_mem_finiteCutExteriorEdges_iff G S x y).1 he
    let x' : {v : V // v ∉ S} := ⟨x, he'.2.1⟩
    let y' : {v : V // v ∉ S} := ⟨y, he'.2.2⟩
    rw [bond_mk, bond_mk]
    change spin (finiteCutMerge S inside outside) x'.1 *
        spin (finiteCutMerge S inside outside) y'.1 =
      spin (finiteCutMerge S inside' outside) x'.1 *
        spin (finiteCutMerge S inside' outside) y'.1
    simp


theorem sum_bond_finiteCutMerge
    (S : Finset V) (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) :
    (∑ e ∈ G.edgeFinset, bond (finiteCutMerge S inside outside) e) =
      (∑ e ∈ (finiteCutGraph G S).edgeFinset, bond inside e) +
      (∑ x : {v : V // v ∈ S},
        finiteCutBoundaryField G S outside x * spin inside x) +
      ∑ e ∈ finiteCutExteriorEdges G S,
        bond (finiteCutMerge S inside outside) e := by
  rw [sum_bond_eq_internal_add_cross_add_exterior,
    sum_internal_bond_finiteCutMerge_eq_cutGraph,
    sum_cross_bond_finiteCutMerge_eq_boundaryField]




theorem wJ_finiteCutMerge_factor
    (beta : Real) (S : Finset V)
    (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) :
    wJ G.edgeFinset (fun _ => beta) (fun _ => 0)
        (finiteCutMerge S inside outside) =
      Real.exp (beta * (∑ e ∈ finiteCutExteriorEdges G S,
        bond (finiteCutMerge S inside outside) e)) *
      wJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
        (fun x => beta * finiteCutBoundaryField G S outside x) inside := by
  unfold wJ
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rw [← Finset.mul_sum, sum_bond_finiteCutMerge]
  rw [← Real.exp_add]
  congr 1
  rw [mul_add, mul_add]
  simp_rw [Finset.mul_sum]
  ring



def finiteCutConditionalTwoPoint (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (x y : {v : V // v ∈ S}) : Real :=
  expJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
    (fun z => beta * finiteCutBoundaryField G S outside z)
    (fun sigma => spin sigma x * spin sigma y)


def finiteCutPlusTwoPoint (beta : Real) (S : Finset V)
    (x y : {v : V // v ∈ S}) : Real :=
  expJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
    (fun z => beta * finiteCutPlusBoundaryField G S z)
    (fun sigma => spin sigma x * spin sigma y)


theorem finiteCutConditionalTwoPoint_le_plus
    (beta : Real) (hbeta : 0 ≤ beta) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (x y : {v : V // v ∈ S}) :
    finiteCutConditionalTwoPoint G beta S outside x y ≤
      finiteCutPlusTwoPoint G beta S x y := by
  unfold finiteCutConditionalTwoPoint finiteCutPlusTwoPoint
  apply ginibre_boundary_twoPoint_mono
  · intro e he
    exact hbeta
  · intro z
    rw [abs_mul, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left
      (abs_finiteCutBoundaryField_le_plus G S outside z) hbeta


def finiteCutExteriorFactor (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool) : Real :=
  Real.exp (beta * (∑ e ∈ finiteCutExteriorEdges G S,
    bond (finiteCutMerge S (fun _ => false) outside) e))

theorem finiteCutExteriorFactor_pos (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool) :
    0 < finiteCutExteriorFactor G beta S outside := by
  exact Real.exp_pos _

theorem wJ_finiteCutMerge_factor_fixedExterior
    (beta : Real) (S : Finset V)
    (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) :
    wJ G.edgeFinset (fun _ => beta) (fun _ => 0)
        (finiteCutMerge S inside outside) =
      finiteCutExteriorFactor G beta S outside *
      wJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
        (fun x => beta * finiteCutBoundaryField G S outside x) inside := by
  rw [wJ_finiteCutMerge_factor]
  congr 1
  unfold finiteCutExteriorFactor
  congr 2
  exact sum_exterior_bond_finiteCutMerge_eq G S inside (fun _ => false) outside


def finiteCutConditionalZ (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool) : Real :=
  ZJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
    (fun x => beta * finiteCutBoundaryField G S outside x)


def finiteCutConditionalPairNumerator (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (x y : {v : V // v ∈ S}) : Real :=
  ∑ inside : ConfigSpace {v : V // v ∈ S},
    (spin inside x * spin inside y) *
      wJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
        (fun z => beta * finiteCutBoundaryField G S outside z) inside

theorem finiteCutConditionalTwoPoint_eq_div
    (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (x y : {v : V // v ∈ S}) :
    finiteCutConditionalTwoPoint G beta S outside x y =
      finiteCutConditionalPairNumerator G beta S outside x y /
        finiteCutConditionalZ G beta S outside := by
  rfl



theorem ZJ_eq_sum_finiteCutExteriorFactor_mul_conditionalZ
    (beta : Real) (S : Finset V) :
    ZJ G.edgeFinset (fun _ => beta) (fun _ => 0) =
      ∑ outside : {v : V // v ∉ S} → Bool,
        finiteCutExteriorFactor G beta S outside *
          finiteCutConditionalZ G beta S outside := by
  unfold ZJ
  rw [← Equiv.sum_comp (ghsvp_splitConfig S).symm
    (fun sigma => wJ G.edgeFinset (fun _ => beta) (fun _ => 0) sigma)]
  simp only [ghsvp_splitConfig, Equiv.coe_fn_symm_mk]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Prod.fst, Prod.snd]
  apply Finset.sum_congr rfl
  intro outside _
  unfold finiteCutConditionalZ ZJ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro inside _
  change wJ G.edgeFinset (fun _ => beta) (fun _ => 0)
      (finiteCutMerge S inside outside) = _
  rw [wJ_finiteCutMerge_factor_fixedExterior]



theorem sum_pair_wJ_eq_sum_finiteCutExteriorFactor_mul_conditionalNumerator
    (beta : Real) (S : Finset V) (x y : {v : V // v ∈ S}) :
    (∑ sigma : ConfigSpace V,
        (spin sigma x.1 * spin sigma y.1) *
          wJ G.edgeFinset (fun _ => beta) (fun _ => 0) sigma) =
      ∑ outside : {v : V // v ∉ S} → Bool,
        finiteCutExteriorFactor G beta S outside *
          finiteCutConditionalPairNumerator G beta S outside x y := by
  rw [← Equiv.sum_comp (ghsvp_splitConfig S).symm
    (fun sigma => (spin sigma x.1 * spin sigma y.1) *
      wJ G.edgeFinset (fun _ => beta) (fun _ => 0) sigma)]
  simp only [ghsvp_splitConfig, Equiv.coe_fn_symm_mk]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Prod.fst, Prod.snd]
  apply Finset.sum_congr rfl
  intro outside _
  unfold finiteCutConditionalPairNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro inside _
  change (spin (finiteCutMerge S inside outside) x.1 *
      spin (finiteCutMerge S inside outside) y.1) *
        wJ G.edgeFinset (fun _ => beta) (fun _ => 0)
          (finiteCutMerge S inside outside) = _
  rw [spin_finiteCutMerge_inside, spin_finiteCutMerge_inside,
    wJ_finiteCutMerge_factor_fixedExterior]
  ring



theorem expJ_pair_le_finiteCutPlusTwoPoint
    (beta : Real) (hbeta : 0 ≤ beta) (S : Finset V)
    (x y : {v : V // v ∈ S}) :
    expJ G.edgeFinset (fun _ => beta) (fun _ => 0)
        (fun sigma => spin sigma x.1 * spin sigma y.1) ≤
      finiteCutPlusTwoPoint G beta S x y := by
  let P := finiteCutPlusTwoPoint G beta S x y
  have hcond (outside : {v : V // v ∉ S} → Bool) :
      finiteCutConditionalPairNumerator G beta S outside x y ≤
        P * finiteCutConditionalZ G beta S outside := by
    have hle := finiteCutConditionalTwoPoint_le_plus
      G beta hbeta S outside x y
    rw [finiteCutConditionalTwoPoint_eq_div] at hle
    exact (div_le_iff₀ (ZJ_pos (finiteCutGraph G S).edgeFinset
      (fun _ => beta)
      (fun z => beta * finiteCutBoundaryField G S outside z))).mp hle
  unfold expJ
  rw [sum_pair_wJ_eq_sum_finiteCutExteriorFactor_mul_conditionalNumerator]
  change _ ≤ P
  apply (div_le_iff₀ (ZJ_pos G.edgeFinset (fun _ => beta) (fun _ => 0))).2
  calc
    (∑ outside : {v : V // v ∉ S} → Bool,
        finiteCutExteriorFactor G beta S outside *
          finiteCutConditionalPairNumerator G beta S outside x y) ≤
        ∑ outside : {v : V // v ∉ S} → Bool,
          finiteCutExteriorFactor G beta S outside *
            (P * finiteCutConditionalZ G beta S outside) := by
      exact Finset.sum_le_sum fun outside _ =>
        mul_le_mul_of_nonneg_left (hcond outside)
          (finiteCutExteriorFactor_pos G beta S outside).le
    _ = P * ∑ outside : {v : V // v ∉ S} → Bool,
          finiteCutExteriorFactor G beta S outside *
            finiteCutConditionalZ G beta S outside := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro outside _
      ring
    _ = P * ZJ G.edgeFinset (fun _ => beta) (fun _ => 0) := by
      rw [ZJ_eq_sum_finiteCutExteriorFactor_mul_conditionalZ]



theorem isingTorusTwoPoint_le_finiteCutPlus
    {d k : Nat} (beta : Real) (hbeta : 0 ≤ beta)
    (S : Finset (IsingDyadicTorus d k)) (x y : {v // v ∈ S}) :
    isingTorusTwoPoint beta x.1 y.1 ≤
      finiteCutPlusTwoPoint (isingTorusGraph d k) beta S x y := by
  rw [isingTorusTwoPoint_eq_twoPointJ]
  unfold twoPointJ
  rw [expectationJ_eq_expJ]
  simp only [mul_one]
  have hle := expJ_pair_le_finiteCutPlusTwoPoint
    (isingTorusGraph d k) beta hbeta S x y
  have hfun : spinProd (sourcePair x.1 y.1) =
      fun sigma => spin sigma x.1 * spin sigma y.1 := by
    funext sigma
    exact spinProd_sourcePair sigma x.1 y.1
  rw [hfun]
  exact hle



theorem finiteCutPlusTwoPoint_eq_vertexFieldTwoPoint
    (beta : Real) (S : Finset V) (x y : {v // v ∈ S}) :
    finiteCutPlusTwoPoint G beta S x y =
      vertexFieldTwoPoint (finiteCutGraph G S) beta
        (unitEdgeCoupling (finiteCutGraph G S))
        (finiteCutPlusBoundaryField G S) x y := by
  unfold finiteCutPlusTwoPoint vertexFieldTwoPoint vertexFieldExpectation
  have hweight (sigma : ConfigSpace {v : V // v ∈ S}) :
      wJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
          (fun z => beta * finiteCutPlusBoundaryField G S z) sigma =
        vertexFieldWeight (finiteCutGraph G S) beta
          (unitEdgeCoupling (finiteCutGraph G S))
          (finiteCutPlusBoundaryField G S) sigma := by
    unfold wJ vertexFieldWeight
    congr 1
    have hedge : (∑ e ∈ (finiteCutGraph G S).edgeFinset,
        unitEdgeCoupling (finiteCutGraph G S) e * bond sigma e) =
        ∑ e ∈ (finiteCutGraph G S).edgeFinset, bond sigma e := by
      apply Finset.sum_congr rfl
      intro e he
      rw [unitEdgeCoupling_edgeFinset (finiteCutGraph G S) he, one_mul]
    rw [hedge, mul_add]
    simp_rw [Finset.mul_sum]
    ring
  have hZ : ZJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
      (fun z => beta * finiteCutPlusBoundaryField G S z) =
      vertexFieldZ (finiteCutGraph G S) beta
        (unitEdgeCoupling (finiteCutGraph G S))
        (finiteCutPlusBoundaryField G S) := by
    unfold ZJ vertexFieldZ
    exact Finset.sum_congr rfl fun sigma _ => hweight sigma
  unfold expJ
  rw [hZ]
  congr 1
  apply Finset.sum_congr rfl
  intro sigma _
  rw [spinProd_sourcePair, hweight]



theorem expJ_pair_beta_field_eq_vertexFieldTwoPoint
    (beta : Real) (field : V → Real) (x y : V) :
    expJ G.edgeFinset (fun _ => beta) (fun z => beta * field z)
        (fun sigma => spin sigma x * spin sigma y) =
      vertexFieldTwoPoint G beta (unitEdgeCoupling G) field x y := by
  unfold expJ vertexFieldTwoPoint vertexFieldExpectation
  have hweight (sigma : ConfigSpace V) :
      wJ G.edgeFinset (fun _ => beta) (fun z => beta * field z) sigma =
        vertexFieldWeight G beta (unitEdgeCoupling G) field sigma := by
    unfold wJ vertexFieldWeight
    congr 1
    have hedge : (∑ e ∈ G.edgeFinset,
        unitEdgeCoupling G e * bond sigma e) =
        ∑ e ∈ G.edgeFinset, bond sigma e := by
      apply Finset.sum_congr rfl
      intro e he
      rw [unitEdgeCoupling_edgeFinset G he, one_mul]
    rw [hedge, mul_add]
    simp_rw [Finset.mul_sum]
    ring
  have hZ : ZJ G.edgeFinset (fun _ => beta) (fun z => beta * field z) =
      vertexFieldZ G beta (unitEdgeCoupling G) field := by
    unfold ZJ vertexFieldZ
    exact Finset.sum_congr rfl fun sigma _ => hweight sigma
  rw [hZ]
  congr 1
  apply Finset.sum_congr rfl
  intro sigma _
  rw [spinProd_sourcePair, hweight]

section Relabel

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]



theorem expJ_pair_const_relabel (e : V ≃ W)
    (hadj : ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y))
    (beta : Real) (fieldV : V → Real) (fieldW : W → Real)
    (hfield : ∀ x, fieldV x = fieldW (e x)) (x y : V) :
    expJ G.edgeFinset (fun _ => beta) fieldV
        (fun sigma => spin sigma x * spin sigma y) =
      expJ H.edgeFinset (fun _ => beta) fieldW
        (fun sigma => spin sigma (e x) * spin sigma (e y)) := by
  unfold expJ
  rw [ghsi_ZJ_const_relabel G H e hadj beta fieldV fieldW hfield]
  rw [← Equiv.sum_comp (isingCfgEquiv e)
    (fun omega => (spin omega x * spin omega y) *
      wJ G.edgeFinset (fun _ => beta) fieldV omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro omega _
  rw [spin_isingCfgEquiv, spin_isingCfgEquiv,
    ghsi_wJ_const_relabel G H e hadj beta fieldV fieldW hfield]



theorem finiteCutPlusTwoPoint_relabel
    (S : Finset V) (T : Finset W)
    (e : {v : V // v ∈ S} ≃ {w : W // w ∈ T})
    (hadj : ∀ x y,
      (finiteCutGraph G S).Adj x y ↔
        (finiteCutGraph H T).Adj (e x) (e y))
    (hfield : ∀ x, finiteCutPlusBoundaryField G S x =
      finiteCutPlusBoundaryField H T (e x))
    (beta : Real) (x y : {v : V // v ∈ S}) :
    finiteCutPlusTwoPoint G beta S x y =
      finiteCutPlusTwoPoint H beta T (e x) (e y) := by
  unfold finiteCutPlusTwoPoint
  apply expJ_pair_const_relabel
    (finiteCutGraph G S) (finiteCutGraph H T) e hadj beta
      (fun z => beta * finiteCutPlusBoundaryField G S z)
      (fun z => beta * finiteCutPlusBoundaryField H T z)
      (fun z => congrArg (fun r : Real => beta * r) (hfield z)) x y

end Relabel



theorem finiteCutPlusTwoPoint_torusImage_eq_gvPlus_of_field
    {d k R : Nat} (S : Finset (Site d))
    (hS : (↑S : Set (Site d)) ⊆ box d R)
    (hside : 2 * (R + 1) < isingDyadicSide k)
    (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
    (hfield : ∀ x : {x // x ∈ S},
      finiteCutPlusBoundaryField (isingTorusGraph d k)
          (isingTorusImageFinset k S) (isingTorusImageEquiv S hinj x) =
        plusBoundaryField S x)
    (beta : Real) (a b : {x // x ∈ S}) :
    finiteCutPlusTwoPoint (isingTorusGraph d k) beta
        (isingTorusImageFinset k S)
        (isingTorusImageEquiv S hinj a)
        (isingTorusImageEquiv S hinj b) =
      ∫ omega, spin omega a.1 * spin omega b.1 ∂(gvPlusMeasure S beta 0) := by
  let e := isingTorusImageEquiv S hinj
  have hadj : ∀ u v : {z // z ∈ isingTorusImageFinset k S},
      (finiteCutGraph (isingTorusGraph d k)
          (isingTorusImageFinset k S)).Adj u v ↔
        (graphS d S).Adj (e.symm u) (e.symm v) := by
    intro u v
    change (isingTorusGraph d k).Adj u.1 v.1 ↔
      (graphS d S).Adj (e.symm u) (e.symm v)
    simpa only [e, Equiv.apply_symm_apply] using
      (isingTorusImageEquiv_adj S hS hside hinj
        (e.symm u) (e.symm v)).symm
  have hfield' : ∀ u : {z // z ∈ isingTorusImageFinset k S},
      beta * finiteCutPlusBoundaryField (isingTorusGraph d k)
          (isingTorusImageFinset k S) u =
        beta * plusBoundaryField S (e.symm u) := by
    intro u
    apply congrArg (fun r : Real => beta * r)
    simpa only [e, Equiv.apply_symm_apply] using hfield (e.symm u)
  unfold finiteCutPlusTwoPoint
  calc
    expJ (finiteCutGraph (isingTorusGraph d k)
          (isingTorusImageFinset k S)).edgeFinset
        (fun _ => beta)
        (fun z => beta * finiteCutPlusBoundaryField (isingTorusGraph d k)
          (isingTorusImageFinset k S) z)
        (fun sigma => spin sigma (e a) * spin sigma (e b)) =
      expJ (graphS d S).edgeFinset (fun _ => beta)
        (fun z => beta * plusBoundaryField S z)
        (fun sigma => spin sigma a * spin sigma b) := by
          simpa only [Equiv.symm_apply_apply] using expJ_pair_const_relabel
            (finiteCutGraph (isingTorusGraph d k)
              (isingTorusImageFinset k S))
            (graphS d S) e.symm hadj beta
            (fun z => beta * finiteCutPlusBoundaryField (isingTorusGraph d k)
              (isingTorusImageFinset k S) z)
            (fun z => beta * plusBoundaryField S z) hfield' (e a) (e b)
    _ = vertexFieldTwoPoint (graphS d S) beta
        (unitEdgeCoupling (graphS d S)) (plusBoundaryField S) a b :=
      expJ_pair_beta_field_eq_vertexFieldTwoPoint
        (graphS d S) beta (plusBoundaryField S) a b
    _ = ∫ omega, spin omega a.1 * spin omega b.1
        ∂(gvPlusMeasure S beta 0) :=
      (gvPlus_pair_eq_vertexField S beta a b).symm


end

end StatMech.FrontierA
