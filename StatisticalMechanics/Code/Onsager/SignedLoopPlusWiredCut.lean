/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopAnchoredCut
import Code.Onsager.SignedLoopLowTempPlus
import Code.Ising.KWGeometricDual









open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section


abbrev ons_PlusWiredVertex (d n : Nat) := Option {x // x ∈ box d n}


abbrev ons_PlusWiredBond (d n : Nat) :=
  {edge // edge ∈ bondFinsetTouch d n}


def ons_plusWiredVertexOfSite (d n : Nat) (x : Site d) :
    ons_PlusWiredVertex d n :=
  if hx : x ∈ box d n then some ⟨x, hx⟩ else none


def ons_plusWiredBondEnds (d n : Nat) (edge : ons_PlusWiredBond d n) :
    ons_PlusWiredVertex d n × ons_PlusWiredVertex d n :=
  (ons_plusWiredVertexOfSite d n edge.1.out.1,
    ons_plusWiredVertexOfSite d n edge.1.out.2)



theorem ons_optionAnchoredEquiv_apply_vertexOfSite
    (d n : Nat) (tau : {x // x ∈ box d n} → Bool) (x : Site d) :
    (ons_optionAnchoredEquiv tau).1 (ons_plusWiredVertexOfSite d n x) =
      !(glue (plusField d) tau x) := by
  by_cases hx : x ∈ box d n
  · simp [ons_plusWiredVertexOfSite, hx, glue, ons_optionAnchoredEquiv]
  · simp [ons_plusWiredVertexOfSite, hx, glue, plusField,
      ons_optionAnchoredEquiv]



theorem mem_plusWiredCut_iff
    (d n : Nat) (tau : {x // x ∈ box d n} → Bool)
    (edge : ons_PlusWiredBond d n) :
    edge ∈ multibondCut (ons_plusWiredBondEnds d n)
        (ons_optionAnchoredEquiv tau).1 ↔
      edge.1 ∈ ons_fvCutEdges (bondFinsetTouch d n)
        (glue (plusField d) tau) := by
  rw [mem_multibondCut]
  change
    (ons_optionAnchoredEquiv tau).1
        (ons_plusWiredVertexOfSite d n edge.1.out.1) ≠
      (ons_optionAnchoredEquiv tau).1
        (ons_plusWiredVertexOfSite d n edge.1.out.2) ↔ _
  rw [ons_optionAnchoredEquiv_apply_vertexOfSite,
    ons_optionAnchoredEquiv_apply_vertexOfSite]
  unfold ons_fvCutEdges
  rw [Finset.mem_filter]
  simp only [edge.2, true_and]
  rw [← kwg_isSplit_iff_bond_neg]
  have hout : s(edge.1.out.1, edge.1.out.2) = edge.1 := by
    change Sym2.mk edge.1.out.1 edge.1.out.2 = edge.1
    rw [Sym2.mk, edge.1.out_eq]
  have hsplit : kwg_isSplit (glue (plusField d) tau) edge.1 ↔
      glue (plusField d) tau edge.1.out.1 ≠
        glue (plusField d) tau edge.1.out.2 := by
    calc
      kwg_isSplit (glue (plusField d) tau) edge.1 ↔
          kwg_isSplit (glue (plusField d) tau)
            s(edge.1.out.1, edge.1.out.2) := by rw [hout]
      _ ↔ _ := kwg_isSplit_mk _ _ _
  rw [hsplit]
  cases glue (plusField d) tau edge.1.out.1 <;>
    cases glue (plusField d) tau edge.1.out.2 <;> simp


def ons_plusWiredCutLattice
    (d n : Nat) (tau : {x // x ∈ box d n} → Bool) :
    Finset (Sym2 (Site d)) :=
  (multibondCut (ons_plusWiredBondEnds d n)
    (ons_optionAnchoredEquiv tau).1).map
      ⟨Subtype.val, Subtype.val_injective⟩


theorem ons_plusWiredCutLattice_eq_fvCutEdges
    (d n : Nat) (tau : {x // x ∈ box d n} → Bool) :
    ons_plusWiredCutLattice d n tau =
      ons_fvCutEdges (bondFinsetTouch d n) (glue (plusField d) tau) := by
  ext edge
  constructor
  · intro hedge
    rw [ons_plusWiredCutLattice, Finset.mem_map] at hedge
    obtain ⟨typed, htyped, rfl⟩ := hedge
    exact (mem_plusWiredCut_iff d n tau typed).mp htyped
  · intro hedge
    have hedgeB : edge ∈ bondFinsetTouch d n := by
      exact (Finset.mem_filter.mp hedge).1
    let typed : ons_PlusWiredBond d n := ⟨edge, hedgeB⟩
    rw [ons_plusWiredCutLattice, Finset.mem_map]
    exact ⟨typed, (mem_plusWiredCut_iff d n tau typed).mpr hedge, rfl⟩



theorem card_plusWiredCut_eq_fvCutEdges
    (d n : Nat) (tau : {x // x ∈ box d n} → Bool) :
    (multibondCut (ons_plusWiredBondEnds d n)
        (ons_optionAnchoredEquiv tau).1).card =
      (ons_fvCutEdges (bondFinsetTouch d n)
        (glue (plusField d) tau)).card := by
  rw [← ons_plusWiredCutLattice_eq_fvCutEdges d n tau,
    ons_plusWiredCutLattice, Finset.card_map]


def ons_plusWiredContourDenominator (d n : Nat) (beta : Real) : Real :=
  ∑ config : AnchoredConfig (ons_PlusWiredVertex d n) none,
    Real.exp (-2 * beta) ^
      (multibondCut (ons_plusWiredBondEnds d n) config.1).card



theorem ons_plusLowTempContourDenominator_eq_wired
    (d n : Nat) (beta : Real) :
    ons_plusLowTempContourDenominator d n beta =
      ons_plusWiredContourDenominator d n beta := by
  unfold ons_plusLowTempContourDenominator ons_plusWiredContourDenominator
  calc
    (∑ tau : {x // x ∈ box d n} → Bool,
      Real.exp (-2 * beta) ^
        (ons_fvCutEdges (bondFinsetTouch d n)
          (glue (plusField d) tau)).card) =
        ∑ tau : {x // x ∈ box d n} → Bool,
          Real.exp (-2 * beta) ^
            (multibondCut (ons_plusWiredBondEnds d n)
              (ons_optionAnchoredEquiv tau).1).card := by
      apply Finset.sum_congr rfl
      intro tau _
      rw [card_plusWiredCut_eq_fvCutEdges]
    _ = _ := optionInteriorCutSum_eq_anchored
      (ons_plusWiredBondEnds d n)
      (fun cut => Real.exp (-2 * beta) ^ cut.card)


def ons_plusWiredEndpointSign
    (d n : Nat) (config : ConfigSpace (ons_PlusWiredVertex d n))
    (u v : Site d) : Real :=
  spin config (ons_plusWiredVertexOfSite d n u) *
    spin config (ons_plusWiredVertexOfSite d n v)



theorem ons_plusWiredEndpointSign_eq_pathSign
    (d n : Nat) (tau : {x // x ∈ box d n} → Bool)
    {u v : Site d} (path : (hypercubicLattice d).Walk u v) :
    ons_plusWiredEndpointSign d n (ons_optionAnchoredEquiv tau).1 u v =
      ons_plusLowTempPathSign (glue (plusField d) tau) path := by
  rw [ons_plusLowTempPathSign_eq_spin_mul]
  unfold ons_plusWiredEndpointSign
  unfold spin
  rw [ons_optionAnchoredEquiv_apply_vertexOfSite,
    ons_optionAnchoredEquiv_apply_vertexOfSite]
  cases glue (plusField d) tau u <;>
    cases glue (plusField d) tau v <;> norm_num


def ons_plusWiredPathNumerator
    (d n : Nat) (beta : Real) (u v : Site d) : Real :=
  ∑ config : AnchoredConfig (ons_PlusWiredVertex d n) none,
    ons_plusWiredEndpointSign d n config.1 u v *
      Real.exp (-2 * beta) ^
        (multibondCut (ons_plusWiredBondEnds d n) config.1).card



theorem ons_plusLowTempPathNumerator_eq_wired
    (d n : Nat) (beta : Real) {u v : Site d}
    (path : (hypercubicLattice d).Walk u v) :
    ons_plusLowTempPathNumerator d n beta path =
      ons_plusWiredPathNumerator d n beta u v := by
  unfold ons_plusLowTempPathNumerator ons_plusWiredPathNumerator
  calc
    (∑ tau : {x // x ∈ box d n} → Bool,
      ons_plusLowTempPathSign (glue (plusField d) tau) path *
        Real.exp (-2 * beta) ^
          (ons_fvCutEdges (bondFinsetTouch d n)
            (glue (plusField d) tau)).card) =
        ∑ tau : {x // x ∈ box d n} → Bool,
          ons_plusWiredEndpointSign d n (ons_optionAnchoredEquiv tau).1 u v *
            Real.exp (-2 * beta) ^
              (multibondCut (ons_plusWiredBondEnds d n)
                (ons_optionAnchoredEquiv tau).1).card := by
      apply Finset.sum_congr rfl
      intro tau _
      rw [ons_plusWiredEndpointSign_eq_pathSign,
        card_plusWiredCut_eq_fvCutEdges]
    _ = _ := by
      rw [← (ons_optionAnchoredEquiv
        (I := {x // x ∈ box d n})).sum_comp]



theorem integral_plusMeasure_twoPoint_eq_wiredCutRatio
    (d n : Nat) (beta : Real) {u v : Site d}
    (path : (hypercubicLattice d).Walk u v) :
    (∫ config, spin config u * spin config v
        ∂(plusMeasure d n beta 0 : MeasureTheory.Measure
          (ConfigSpace (Site d)))) =
      ons_plusWiredPathNumerator d n beta u v /
        ons_plusWiredContourDenominator d n beta := by
  rw [integral_plusMeasure_twoPoint_eq_lowTempPathRatio d n beta path,
    ons_plusLowTempPathNumerator_eq_wired d n beta path,
    ons_plusLowTempContourDenominator_eq_wired d n beta]

end

end StatMech.Onsager
