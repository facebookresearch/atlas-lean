/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.GinibreBoundaryDerivative

open scoped BigOperators
open Finset Filter Topology

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def ginibreChainEdge {N : Nat} (v : Nat -> V) (j : Fin N) : Sym2 V :=
  s(v j.val, v (j.val + 1))





theorem boundaryInterfaceFreeEnergy_deriv_ge_chainDeficit
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hPlus h : V -> Real)
    (hJ : forall e, e ∈ E -> 0 <= J e)
    (hdom : forall x, |h x| <= hPlus x)
    (beta : Real) (hbeta : 0 <= beta)
    (v : Nat -> V) (N : Nat)
    (hinj : Function.Injective (ginibreChainEdge (N := N) v))
    (hedge : forall j : Fin N, ginibreChainEdge v j ∈ E)
    (hunit : forall j : Fin N, J (ginibreChainEdge v j) = 1) :
    (∑ j : Fin N,
        (expJ E (fun a => beta * J a) (fun x => beta * hPlus x)
              (fun s => bond s (ginibreChainEdge v j)) -
          expJ E (fun a => beta * J a) (fun x => beta * h x)
              (fun s => bond s (ginibreChainEdge v j)))) <=
      deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
  let deficit : Sym2 V -> Real := fun e =>
    expJ E (fun a => beta * J a) (fun x => beta * hPlus x)
        (fun s => bond s e) -
      expJ E (fun a => beta * J a) (fun x => beta * h x)
        (fun s => bond s e)
  let chainEdges : Finset (Sym2 V) :=
    Finset.univ.image (ginibreChainEdge (N := N) v)
  have hJbeta : forall e, e ∈ E -> 0 <= beta * J e := by
    intro e he
    exact mul_nonneg hbeta (hJ e he)
  have hdomBeta : forall x, |beta * h x| <= beta * hPlus x := by
    intro x
    rw [abs_mul, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left (hdom x) hbeta
  have hchainEdgesSubset : chainEdges ⊆ E := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨j, _, rfl⟩ := he
    exact hedge j
  have hdeficit_nonneg : forall e, e ∈ E -> 0 <= deficit e := by
    intro e he
    exact sub_nonneg.mpr (ginibre_boundary_bond_mono E
      (fun a => beta * J a) (fun x => beta * hPlus x)
      (fun x => beta * h x) hJbeta hdomBeta e)
  have hselected :
      (∑ e ∈ chainEdges, J e * deficit e) =
        ∑ j : Fin N, deficit (ginibreChainEdge v j) := by
    rw [Finset.sum_image (s := Finset.univ) hinj.injOn]
    apply Finset.sum_congr rfl
    intro j _
    rw [hunit]
    ring
  have hbond :
      (∑ j : Fin N, deficit (ginibreChainEdge v j)) <=
        ∑ e ∈ E, J e * deficit e := by
    rw [← hselected]
    apply Finset.sum_le_sum_of_subset_of_nonneg hchainEdgesSubset
    intro e he _
    exact mul_nonneg (hJ e he) (hdeficit_nonneg e he)
  have hfield : 0 <=
      ((∑ x : V, hPlus x *
          expJ E (fun e => beta * J e) (fun y => beta * hPlus y)
            (fun s => spin s x)) -
        (∑ x : V, h x *
          expJ E (fun e => beta * J e) (fun y => beta * h y)
            (fun s => spin s x))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun x _ =>
      ginibre_boundary_fieldTerm_nonneg E J hPlus h hJ hdom beta hbeta x
  calc
    (∑ j : Fin N,
        (expJ E (fun a => beta * J a) (fun x => beta * hPlus x)
              (fun s => bond s (ginibreChainEdge v j)) -
          expJ E (fun a => beta * J a) (fun x => beta * h x)
              (fun s => bond s (ginibreChainEdge v j)))) =
        ∑ j : Fin N, deficit (ginibreChainEdge v j) := rfl
    _ <= ∑ e ∈ E, J e * deficit e := hbond
    _ <= (∑ e ∈ E, J e * deficit e) +
        ((∑ x : V, hPlus x *
            expJ E (fun e => beta * J e) (fun y => beta * hPlus y)
              (fun s => spin s x)) -
          (∑ x : V, h x *
            expJ E (fun e => beta * J e) (fun y => beta * h y)
              (fun s => spin s x))) := le_add_of_nonneg_right hfield
    _ = deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
      rw [(hasDerivAt_boundaryInterfaceFreeEnergy E J hPlus h beta).deriv,
        scaledMeanInteraction_eq_bonds_add_fields,
        scaledMeanInteraction_eq_bonds_add_fields, add_sub_add_comm]
      unfold deficit
      apply congrArg₂ (· + ·)
      · rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro e _
        ring
      · rfl





theorem boundaryInterfaceFreeEnergy_deriv_ge_chainCross
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hPlus h : V -> Real)
    (hJ : forall e, e ∈ E -> 0 <= J e)
    (hdom : forall x, |h x| <= hPlus x)
    (beta : Real) (hbeta : 0 <= beta)
    (v : Nat -> V) (N : Nat)
    (hinj : Function.Injective (ginibreChainEdge (N := N) v))
    (hedge : forall j : Fin N, ginibreChainEdge v j ∈ E)
    (hunit : forall j : Fin N, J (ginibreChainEdge v j) = 1) :
    (∑ j : Fin N,
      (expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
          (fun s => spin s (v j.val)) *
        expJ E (fun e => beta * J e) (fun x => beta * h x)
          (fun s => spin s (v (j.val + 1))) -
       expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
          (fun s => spin s (v (j.val + 1))) *
        expJ E (fun e => beta * J e) (fun x => beta * h x)
          (fun s => spin s (v j.val)))) <=
      deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
  have hJbeta : forall e, e ∈ E -> 0 <= beta * J e := by
    intro e he
    exact mul_nonneg hbeta (hJ e he)
  have hdomBeta : forall x, |beta * h x| <= beta * hPlus x := by
    intro x
    rw [abs_mul, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left (hdom x) hbeta
  have hcross :
      (∑ j : Fin N,
        (expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
            (fun s => spin s (v j.val)) *
          expJ E (fun e => beta * J e) (fun x => beta * h x)
            (fun s => spin s (v (j.val + 1))) -
         expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
            (fun s => spin s (v (j.val + 1))) *
          expJ E (fun e => beta * J e) (fun x => beta * h x)
            (fun s => spin s (v j.val)))) <=
        ∑ j : Fin N,
          (expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
                (fun s => bond s (ginibreChainEdge v j)) -
            expJ E (fun e => beta * J e) (fun x => beta * h x)
                (fun s => bond s (ginibreChainEdge v j))) := by
    apply Finset.sum_le_sum
    intro j _
    simpa [ginibreChainEdge, bond_mk] using
      (ginibre_boundary_correlation E (fun e => beta * J e)
        (fun x => beta * hPlus x) (fun x => beta * h x)
        hJbeta hdomBeta (v j.val) (v (j.val + 1)))
  exact hcross.trans
    (boundaryInterfaceFreeEnergy_deriv_ge_chainDeficit E J hPlus h
      hJ hdom beta hbeta v N hinj hedge hunit)





theorem boundaryInterfaceFreeEnergy_deriv_ge_extendedChainAbsCross
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hPlus h : V -> Real)
    (hJ : forall e, e ∈ E -> 0 <= J e)
    (hdom : forall x, |h x| <= hPlus x)
    (beta : Real) (hbeta : 0 <= beta)
    (v : Nat -> V) (N : Nat)
    (hinj : Function.Injective (ginibreChainEdge (N := N) v))
    (hedge : forall j : Fin N, ginibreChainEdge v j ∈ E)
    (hunit : forall j : Fin N, J (ginibreChainEdge v j) = 1)
    (hend : v 0 ≠ v N)
    (hplusTop : hPlus (v 0) = 1) (hmixTop : h (v 0) = -1)
    (hplusBottom : hPlus (v N) = 1) (hmixBottom : h (v N) = 1) :
    (expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
          (fun s => spin s (v 0)) +
        expJ E (fun e => beta * J e) (fun x => beta * h x)
          (fun s => spin s (v 0))) +
      (∑ j : Fin N, |expJ E (fun e => beta * J e)
            (fun x => beta * hPlus x) (fun s => spin s (v j.val)) *
          expJ E (fun e => beta * J e)
            (fun x => beta * h x) (fun s => spin s (v (j.val + 1))) -
        expJ E (fun e => beta * J e)
            (fun x => beta * hPlus x) (fun s => spin s (v (j.val + 1))) *
          expJ E (fun e => beta * J e)
            (fun x => beta * h x) (fun s => spin s (v j.val))|) +
      (expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
          (fun s => spin s (v N)) -
        expJ E (fun e => beta * J e) (fun x => beta * h x)
          (fun s => spin s (v N))) <=
      deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
  let p : V -> Real := fun x =>
    expJ E (fun e => beta * J e) (fun y => beta * hPlus y)
      (fun s => spin s x)
  let q : V -> Real := fun x =>
    expJ E (fun e => beta * J e) (fun y => beta * h y)
      (fun s => spin s x)
  let deficit : Sym2 V -> Real := fun e =>
    expJ E (fun a => beta * J a) (fun x => beta * hPlus x)
        (fun s => bond s e) -
      expJ E (fun a => beta * J a) (fun x => beta * h x)
        (fun s => bond s e)
  let fieldDef : V -> Real := fun x => hPlus x * p x - h x * q x
  have hJbeta : forall e, e ∈ E -> 0 <= beta * J e := by
    intro e he
    exact mul_nonneg hbeta (hJ e he)
  have hdomBeta : forall x, |beta * h x| <= beta * hPlus x := by
    intro x
    rw [abs_mul, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left (hdom x) hbeta
  have hdeficit_nonneg : forall e, e ∈ E -> 0 <= deficit e := by
    intro e he
    exact sub_nonneg.mpr (ginibre_boundary_bond_mono E
      (fun a => beta * J a) (fun x => beta * hPlus x)
      (fun x => beta * h x) hJbeta hdomBeta e)
  have hfield_nonneg : forall x, 0 <= fieldDef x := by
    intro x
    exact ginibre_boundary_fieldTerm_nonneg E J hPlus h hJ hdom
      beta hbeta x
  have habs (j : Fin N) :
      |p (v j.val) * q (v (j.val + 1)) -
          p (v (j.val + 1)) * q (v j.val)| <=
        deficit (ginibreChainEdge v j) := by
    have hxy := ginibre_boundary_correlation E
      (fun e => beta * J e) (fun x => beta * hPlus x)
      (fun x => beta * h x) hJbeta hdomBeta
      (v j.val) (v (j.val + 1))
    have hyx := ginibre_boundary_correlation E
      (fun e => beta * J e) (fun x => beta * hPlus x)
      (fun x => beta * h x) hJbeta hdomBeta
      (v (j.val + 1)) (v j.val)
    have hpCorr :
        expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
            (fun s => spin s (v (j.val + 1)) * spin s (v j.val)) =
          expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
            (fun s => spin s (v j.val) * spin s (v (j.val + 1))) := by
      congr 1
      funext s
      ring
    have hmCorr :
        expJ E (fun e => beta * J e) (fun x => beta * h x)
            (fun s => spin s (v (j.val + 1)) * spin s (v j.val)) =
          expJ E (fun e => beta * J e) (fun x => beta * h x)
            (fun s => spin s (v j.val) * spin s (v (j.val + 1))) := by
      congr 1
      funext s
      ring
    rw [hpCorr, hmCorr] at hyx
    rw [abs_le]
    constructor
    · dsimp [p, q, deficit]
      simp only [ginibreChainEdge, bond_mk]
      linarith [hyx]
    · simpa [p, q, deficit, ginibreChainEdge, bond_mk] using hxy
  let chainEdges : Finset (Sym2 V) :=
    Finset.univ.image (ginibreChainEdge (N := N) v)
  have hchainSubset : chainEdges ⊆ E := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨j, _, rfl⟩ := he
    exact hedge j
  have hbond :
      (∑ j : Fin N,
        |p (v j.val) * q (v (j.val + 1)) -
          p (v (j.val + 1)) * q (v j.val)|) <=
        ∑ e ∈ E, J e * deficit e := by
    calc
      _ <= ∑ j : Fin N, deficit (ginibreChainEdge v j) :=
        Finset.sum_le_sum fun j _ => habs j
      _ = ∑ e ∈ chainEdges, J e * deficit e := by
        rw [Finset.sum_image (s := Finset.univ) hinj.injOn]
        apply Finset.sum_congr rfl
        intro j _
        rw [hunit]
        ring
      _ <= _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hchainSubset
        intro e he _
        exact mul_nonneg (hJ e he) (hdeficit_nonneg e he)
  have hfield : fieldDef (v 0) + fieldDef (v N) <=
      ∑ x : V, fieldDef x := by
    calc
      fieldDef (v 0) + fieldDef (v N) =
          ∑ x ∈ ({v 0, v N} : Finset V), fieldDef x := by
        simp [hend]
      _ <= ∑ x ∈ (Finset.univ : Finset V), fieldDef x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro x _ _
        exact hfield_nonneg x
      _ = ∑ x : V, fieldDef x := rfl
  have htotal :
      (∑ e ∈ E, J e * deficit e) + (∑ x : V, fieldDef x) =
        deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
    rw [(hasDerivAt_boundaryInterfaceFreeEnergy E J hPlus h beta).deriv,
      scaledMeanInteraction_eq_bonds_add_fields,
      scaledMeanInteraction_eq_bonds_add_fields, add_sub_add_comm]
    unfold deficit fieldDef p q
    apply congrArg₂ (· + ·)
    · rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    · rw [← Finset.sum_sub_distrib]
  change (p (v 0) + q (v 0)) +
      (∑ j : Fin N,
        |p (v j.val) * q (v (j.val + 1)) -
          p (v (j.val + 1)) * q (v j.val)|) +
      (p (v N) - q (v N)) <= _
  have hends : (p (v 0) + q (v 0)) + (p (v N) - q (v N)) =
      fieldDef (v 0) + fieldDef (v N) := by
    simp [fieldDef, hplusTop, hmixTop, hplusBottom, hmixBottom]
  rw [← htotal]
  calc
    _ = (∑ j : Fin N,
          |p (v j.val) * q (v (j.val + 1)) -
            p (v (j.val + 1)) * q (v j.val)|) +
        (fieldDef (v 0) + fieldDef (v N)) := by rw [← hends]; ring
    _ <= (∑ e ∈ E, J e * deficit e) +
        (∑ x : V, fieldDef x) := add_le_add hbond hfield




theorem boundaryInterfaceFreeEnergy_deriv_ge_extendedChainFamilyAbsCross
    {I : Type*} [Fintype I] [DecidableEq I]
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hPlus h : V -> Real)
    (hJ : forall e, e ∈ E -> 0 <= J e)
    (hdom : forall x, |h x| <= hPlus x)
    (beta : Real) (hbeta : 0 <= beta)
    (v : I -> Nat -> V) (N : Nat)
    (hinj : Function.Injective
      (fun q : I × Fin N => ginibreChainEdge (v q.1) q.2))
    (hedge : forall i (j : Fin N), ginibreChainEdge (v i) j ∈ E)
    (hunit : forall i (j : Fin N), J (ginibreChainEdge (v i) j) = 1)
    (hendInj : Function.Injective (fun z : I ⊕ I =>
      match z with | .inl i => v i 0 | .inr i => v i N))
    (hplusTop : forall i, 1 <= hPlus (v i 0))
    (hmixTop : forall i, h (v i 0) = -hPlus (v i 0))
    (hplusBottom : forall i, 1 <= hPlus (v i N))
    (hmixBottom : forall i, h (v i N) = hPlus (v i N)) :
    (∑ i : I,
      ((expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
            (fun s => spin s (v i 0)) +
          expJ E (fun e => beta * J e) (fun x => beta * h x)
            (fun s => spin s (v i 0))) +
        (∑ j : Fin N, |expJ E (fun e => beta * J e)
              (fun x => beta * hPlus x) (fun s => spin s (v i j.val)) *
            expJ E (fun e => beta * J e)
              (fun x => beta * h x) (fun s => spin s (v i (j.val + 1))) -
          expJ E (fun e => beta * J e)
              (fun x => beta * hPlus x) (fun s => spin s (v i (j.val + 1))) *
            expJ E (fun e => beta * J e)
              (fun x => beta * h x) (fun s => spin s (v i j.val))|) +
        (expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
            (fun s => spin s (v i N)) -
          expJ E (fun e => beta * J e) (fun x => beta * h x)
            (fun s => spin s (v i N))))) <=
      deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
  let p : V -> Real := fun x =>
    expJ E (fun e => beta * J e) (fun y => beta * hPlus y)
      (fun s => spin s x)
  let q : V -> Real := fun x =>
    expJ E (fun e => beta * J e) (fun y => beta * h y)
      (fun s => spin s x)
  let deficit : Sym2 V -> Real := fun e =>
    expJ E (fun a => beta * J a) (fun x => beta * hPlus x)
        (fun s => bond s e) -
      expJ E (fun a => beta * J a) (fun x => beta * h x)
        (fun s => bond s e)
  let fieldDef : V -> Real := fun x => hPlus x * p x - h x * q x
  have hJbeta : forall e, e ∈ E -> 0 <= beta * J e := by
    intro e he
    exact mul_nonneg hbeta (hJ e he)
  have hdomBeta : forall x, |beta * h x| <= beta * hPlus x := by
    intro x
    rw [abs_mul, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left (hdom x) hbeta
  have hdeficit_nonneg : forall e, e ∈ E -> 0 <= deficit e := by
    intro e he
    exact sub_nonneg.mpr (ginibre_boundary_bond_mono E
      (fun a => beta * J a) (fun x => beta * hPlus x)
      (fun x => beta * h x) hJbeta hdomBeta e)
  have hfield_nonneg : forall x, 0 <= fieldDef x := by
    intro x
    exact ginibre_boundary_fieldTerm_nonneg E J hPlus h hJ hdom
      beta hbeta x
  have habs (i : I) (j : Fin N) :
      |p (v i j.val) * q (v i (j.val + 1)) -
          p (v i (j.val + 1)) * q (v i j.val)| <=
        deficit (ginibreChainEdge (v i) j) := by
    have hxy := ginibre_boundary_correlation E
      (fun e => beta * J e) (fun x => beta * hPlus x)
      (fun x => beta * h x) hJbeta hdomBeta
      (v i j.val) (v i (j.val + 1))
    have hyx := ginibre_boundary_correlation E
      (fun e => beta * J e) (fun x => beta * hPlus x)
      (fun x => beta * h x) hJbeta hdomBeta
      (v i (j.val + 1)) (v i j.val)
    have hpCorr :
        expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
            (fun s => spin s (v i (j.val + 1)) * spin s (v i j.val)) =
          expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
            (fun s => spin s (v i j.val) * spin s (v i (j.val + 1))) := by
      congr 1
      funext s
      ring
    have hmCorr :
        expJ E (fun e => beta * J e) (fun x => beta * h x)
            (fun s => spin s (v i (j.val + 1)) * spin s (v i j.val)) =
          expJ E (fun e => beta * J e) (fun x => beta * h x)
            (fun s => spin s (v i j.val) * spin s (v i (j.val + 1))) := by
      congr 1
      funext s
      ring
    rw [hpCorr, hmCorr] at hyx
    rw [abs_le]
    constructor
    · dsimp [p, q, deficit]
      simp only [ginibreChainEdge, bond_mk]
      linarith [hyx]
    · simpa [p, q, deficit, ginibreChainEdge, bond_mk] using hxy
  let edgeOf : I × Fin N -> Sym2 V := fun z => ginibreChainEdge (v z.1) z.2
  let chainEdges : Finset (Sym2 V) := Finset.univ.image edgeOf
  have hchainSubset : chainEdges ⊆ E := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨z, _, rfl⟩ := he
    exact hedge z.1 z.2
  have hbond :
      (∑ i : I, ∑ j : Fin N,
        |p (v i j.val) * q (v i (j.val + 1)) -
          p (v i (j.val + 1)) * q (v i j.val)|) <=
        ∑ e ∈ E, J e * deficit e := by
    calc
      _ <= ∑ i : I, ∑ j : Fin N, deficit (ginibreChainEdge (v i) j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => habs i j
      _ = ∑ e ∈ chainEdges, J e * deficit e := by
        rw [← Fintype.sum_prod_type']
        rw [Finset.sum_image (s := Finset.univ) hinj.injOn]
        apply Finset.sum_congr rfl
        intro z _
        rw [hunit]
        simp
      _ <= _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hchainSubset
        intro e he _
        exact mul_nonneg (hJ e he) (hdeficit_nonneg e he)
  let endVertex : I ⊕ I -> V := fun z =>
    match z with | .inl i => v i 0 | .inr i => v i N
  let endVertices : Finset V := Finset.univ.image endVertex
  have hfieldSelected :
      (∑ i : I, (fieldDef (v i 0) + fieldDef (v i N))) <=
        ∑ x : V, fieldDef x := by
    calc
      _ = ∑ z : I ⊕ I, fieldDef (endVertex z) := by
        rw [Fintype.sum_sum_type]
        simp only [endVertex]
        rw [Finset.sum_add_distrib]
      _ = ∑ x ∈ endVertices, fieldDef x := by
        rw [Finset.sum_image (s := Finset.univ) hendInj.injOn]
      _ <= ∑ x ∈ (Finset.univ : Finset V), fieldDef x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro x _ _
        exact hfield_nonneg x
      _ = ∑ x : V, fieldDef x := rfl
  have hqabs (x : V) : |q x| <= p x := by
    exact ginibre_boundary_abs_onePoint_le E
      (fun e => beta * J e) (fun y => beta * hPlus y)
      (fun y => beta * h y) hJbeta hdomBeta x
  have hends (i : I) :
      (p (v i 0) + q (v i 0)) + (p (v i N) - q (v i N)) <=
        fieldDef (v i 0) + fieldDef (v i N) := by
    have htop0 : 0 <= p (v i 0) + q (v i 0) := by
      have := (abs_le.mp (hqabs (v i 0))).1
      linarith
    have hbottom0 : 0 <= p (v i N) - q (v i N) := by
      have := (abs_le.mp (hqabs (v i N))).2
      linarith
    have ht : p (v i 0) + q (v i 0) <= fieldDef (v i 0) := by
      simp only [fieldDef, hmixTop i, neg_mul, sub_neg_eq_add, ← mul_add]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hplusTop i) htop0
    have hb : p (v i N) - q (v i N) <= fieldDef (v i N) := by
      simp only [fieldDef, hmixBottom i, ← mul_sub]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hplusBottom i) hbottom0
    exact add_le_add ht hb
  have hfield :
      (∑ i : I, ((p (v i 0) + q (v i 0)) +
        (p (v i N) - q (v i N)))) <= ∑ x : V, fieldDef x :=
    (Finset.sum_le_sum fun i _ => hends i).trans hfieldSelected
  have htotal :
      (∑ e ∈ E, J e * deficit e) + (∑ x : V, fieldDef x) =
        deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
    rw [(hasDerivAt_boundaryInterfaceFreeEnergy E J hPlus h beta).deriv,
      scaledMeanInteraction_eq_bonds_add_fields,
      scaledMeanInteraction_eq_bonds_add_fields, add_sub_add_comm]
    unfold deficit fieldDef p q
    apply congrArg₂ (· + ·)
    · rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    · rw [← Finset.sum_sub_distrib]
  change (∑ i : I, ((p (v i 0) + q (v i 0)) +
      (∑ j : Fin N,
        |p (v i j.val) * q (v i (j.val + 1)) -
          p (v i (j.val + 1)) * q (v i j.val)|) +
      (p (v i N) - q (v i N)))) <= _
  rw [← htotal]
  calc
    _ <= ∑ i : I, ((∑ j : Fin N,
          |p (v i j.val) * q (v i (j.val + 1)) -
            p (v i (j.val + 1)) * q (v i j.val)|) +
        (fieldDef (v i 0) + fieldDef (v i N))) := by
      apply Finset.sum_le_sum
      intro i _
      linarith [hends i]
    _ = (∑ i : I, ∑ j : Fin N,
          |p (v i j.val) * q (v i (j.val + 1)) -
            p (v i (j.val + 1)) * q (v i j.val)|) +
        ∑ i : I, (fieldDef (v i 0) + fieldDef (v i N)) :=
      Finset.sum_add_distrib
    _ <= (∑ e ∈ E, J e * deficit e) +
        (∑ x : V, fieldDef x) := add_le_add hbond hfieldSelected



theorem boundaryInterfaceFreeEnergy_deriv_ge_chain
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hPlus h : V -> Real)
    (hJ : forall e, e ∈ E -> 0 <= J e)
    (hdom : forall x, |h x| <= hPlus x)
    (beta : Real) (hbeta : 0 <= beta)
    (v : Nat -> V) (N : Nat) (m : Real)
    (hinj : Function.Injective (ginibreChainEdge (N := N) v))
    (hedge : forall j : Fin N, ginibreChainEdge v j ∈ E)
    (hunit : forall j : Fin N, J (ginibreChainEdge v j) = 1)
    (hconst : forall j, j <= N ->
      expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
        (fun s => spin s (v j)) = m) :
    m *
        (expJ E (fun e => beta * J e) (fun x => beta * h x)
            (fun s => spin s (v N)) -
          expJ E (fun e => beta * J e) (fun x => beta * h x)
            (fun s => spin s (v 0))) <=
      deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
  have hJbeta : forall e, e ∈ E -> 0 <= beta * J e := by
    intro e he
    exact mul_nonneg hbeta (hJ e he)
  have hdomBeta : forall x, |beta * h x| <= beta * hPlus x := by
    intro x
    rw [abs_mul, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left (hdom x) hbeta
  have htel := ginibre_chain_correlation_telescope E
    (fun e => beta * J e) (fun x => beta * hPlus x)
    (fun x => beta * h x) hJbeta hdomBeta v N m hconst
  have hfinRange :
      (∑ j : Fin N,
        (expJ E (fun a => beta * J a) (fun x => beta * hPlus x)
              (fun s => bond s (ginibreChainEdge v j)) -
          expJ E (fun a => beta * J a) (fun x => beta * h x)
              (fun s => bond s (ginibreChainEdge v j)))) =
        ∑ j ∈ Finset.range N,
          (expJ E (fun a => beta * J a) (fun x => beta * hPlus x)
                (fun s => spin s (v j) * spin s (v (j + 1))) -
            expJ E (fun a => beta * J a) (fun x => beta * h x)
                (fun s => spin s (v j) * spin s (v (j + 1)))) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    simp only [hjN, ↓reduceDIte]
    simp [ginibreChainEdge, bond_mk]
  calc
    m *
        (expJ E (fun e => beta * J e) (fun x => beta * h x)
            (fun s => spin s (v N)) -
          expJ E (fun e => beta * J e) (fun x => beta * h x)
            (fun s => spin s (v 0))) <=
        ∑ j ∈ Finset.range N,
          (expJ E (fun a => beta * J a) (fun x => beta * hPlus x)
                (fun s => spin s (v j) * spin s (v (j + 1))) -
            expJ E (fun a => beta * J a) (fun x => beta * h x)
                (fun s => spin s (v j) * spin s (v (j + 1)))) := htel
    _ = ∑ j : Fin N,
        (expJ E (fun a => beta * J a) (fun x => beta * hPlus x)
              (fun s => bond s (ginibreChainEdge v j)) -
          expJ E (fun a => beta * J a) (fun x => beta * h x)
              (fun s => bond s (ginibreChainEdge v j))) := hfinRange.symm
    _ <= deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta :=
      boundaryInterfaceFreeEnergy_deriv_ge_chainDeficit E J hPlus h
        hJ hdom beta hbeta v N hinj hedge hunit



theorem boundaryInterfaceFreeEnergy_deriv_ge_two_mul_sq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hPlus h : V -> Real)
    (hJ : forall e, e ∈ E -> 0 <= J e)
    (hdom : forall x, |h x| <= hPlus x)
    (beta : Real) (hbeta : 0 <= beta)
    (v : Nat -> V) (N : Nat) (m : Real)
    (hinj : Function.Injective (ginibreChainEdge (N := N) v))
    (hedge : forall j : Fin N, ginibreChainEdge v j ∈ E)
    (hunit : forall j : Fin N, J (ginibreChainEdge v j) = 1)
    (hconst : forall j, j <= N ->
      expJ E (fun e => beta * J e) (fun x => beta * hPlus x)
        (fun s => spin s (v j)) = m)
    (hbottom : expJ E (fun e => beta * J e) (fun x => beta * h x)
      (fun s => spin s (v 0)) = -m)
    (htop : expJ E (fun e => beta * J e) (fun x => beta * h x)
      (fun s => spin s (v N)) = m) :
    2 * m ^ 2 <= deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
  have h := boundaryInterfaceFreeEnergy_deriv_ge_chain E J hPlus h
    hJ hdom beta hbeta v N m hinj hedge hunit hconst
  rw [hbottom, htop] at h
  nlinarith


theorem sum_fin_succ_sub_castSucc (N : Nat) (q : Fin (N + 1) -> Real) :
    (∑ j : Fin N, (q j.succ - q j.castSucc)) =
      q (Fin.last N) - q 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Fin.sum_univ_succ]
      have h := ih (fun i : Fin (N + 1) => q i.succ)
      have h' :
          (∑ i : Fin N, (q i.succ.succ - q i.succ.castSucc)) =
            q (Fin.last N).succ - q (Fin.succ 0) := by
        simpa only [Fin.succ_castSucc] using h
      rw [h']
      rw [show (Fin.last N).succ = Fin.last (N + 1) by
        apply Fin.ext
        simp [Fin.last]]
      rw [show (Fin.castSucc 0 : Fin (N + 1 + 1)) = 0 by rfl]
      ring




theorem extendedChain_absCross_ge_two_mul_sq
    (N : Nat) (p q : Fin (N + 1) -> Real) (m : Real)
    (hm : 0 <= m) (hm1 : m <= 1)
    (hp : forall j, m <= p j)
    (hq : forall j, |q j| <= p j) :
    2 * m ^ 2 <=
      (p 0 + q 0) +
        (∑ j : Fin N,
          |p j.castSucc * q j.succ - p j.succ * q j.castSucc|) +
        (p (Fin.last N) - q (Fin.last N)) := by
  by_cases hmzero : m = 0
  · subst m
    have htop : 0 <= p 0 + q 0 := by
      have := (abs_le.mp (hq 0)).1
      linarith
    have hbottom : 0 <= p (Fin.last N) - q (Fin.last N) := by
      have := (abs_le.mp (hq (Fin.last N))).2
      linarith
    have hsum : 0 <= ∑ j : Fin N,
        |p j.castSucc * q j.succ - p j.succ * q j.castSucc| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    norm_num
    linarith
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hmzero)
  have hp_pos (j : Fin (N + 1)) : 0 < p j := lt_of_lt_of_le hmpos (hp j)
  let r : Fin (N + 1) -> Real := fun j => q j / p j
  have hr_lower (j : Fin (N + 1)) : -1 <= r j := by
    have hj := (abs_le.mp (hq j)).1
    dsimp [r]
    exact (le_div_iff₀ (hp_pos j)).mpr (by linarith)
  have hr_upper (j : Fin (N + 1)) : r j <= 1 := by
    have hj := (abs_le.mp (hq j)).2
    dsimp [r]
    exact (div_le_iff₀ (hp_pos j)).mpr (by linarith)
  have hm_sq_le_p (j : Fin (N + 1)) : m ^ 2 <= p j := by
    nlinarith [hp j]
  have htop : m ^ 2 * |r 0 + 1| <= p 0 + q 0 := by
    have hr0 : 0 <= r 0 + 1 := by linarith [hr_lower 0]
    rw [abs_of_nonneg hr0]
    have heq : p 0 + q 0 = p 0 * (r 0 + 1) := by
      dsimp [r]
      field_simp [(hp_pos 0).ne']
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hm_sq_le_p 0) hr0
  have hbottom : m ^ 2 * |1 - r (Fin.last N)| <=
      p (Fin.last N) - q (Fin.last N) := by
    have hrN : 0 <= 1 - r (Fin.last N) := by
      linarith [hr_upper (Fin.last N)]
    rw [abs_of_nonneg hrN]
    have heq : p (Fin.last N) - q (Fin.last N) =
        p (Fin.last N) * (1 - r (Fin.last N)) := by
      dsimp [r]
      field_simp [(hp_pos (Fin.last N)).ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hm_sq_le_p (Fin.last N)) hrN
  have hstep (j : Fin N) :
      m ^ 2 * |r j.succ - r j.castSucc| <=
        |p j.castSucc * q j.succ - p j.succ * q j.castSucc| := by
    have hprod : m ^ 2 <= p j.castSucc * p j.succ := by
      have := mul_le_mul (hp j.castSucc) (hp j.succ) hm
        (le_trans hm (hp j.castSucc))
      nlinarith
    have hprod0 : 0 <= p j.castSucc * p j.succ :=
      (mul_pos (hp_pos j.castSucc) (hp_pos j.succ)).le
    have heq :
        p j.castSucc * q j.succ - p j.succ * q j.castSucc =
          (p j.castSucc * p j.succ) * (r j.succ - r j.castSucc) := by
      dsimp [r]
      field_simp [(hp_pos j.castSucc).ne', (hp_pos j.succ).ne']
    rw [heq, abs_mul, abs_of_nonneg hprod0]
    exact mul_le_mul_of_nonneg_right hprod (abs_nonneg _)
  have hsteps :
      m ^ 2 * (∑ j : Fin N, |r j.succ - r j.castSucc|) <=
        ∑ j : Fin N,
          |p j.castSucc * q j.succ - p j.succ * q j.castSucc| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hstep j
  have hvariation :
      |r (Fin.last N) - r 0| <=
        ∑ j : Fin N, |r j.succ - r j.castSucc| := by
    rw [← sum_fin_succ_sub_castSucc N r]
    exact Finset.abs_sum_le_sum_abs _ _
  have htriangle :
      2 <= |r 0 + 1| + |r (Fin.last N) - r 0| +
        |1 - r (Fin.last N)| := by
    calc
      2 = |(r 0 + 1) + (r (Fin.last N) - r 0) +
          (1 - r (Fin.last N))| := by ring_nf; norm_num
      _ <= |r 0 + 1| + |r (Fin.last N) - r 0| +
          |1 - r (Fin.last N)| := by
        calc
          _ <= |(r 0 + 1) + (r (Fin.last N) - r 0)| +
              |1 - r (Fin.last N)| :=
            abs_add_le ((r 0 + 1) + (r (Fin.last N) - r 0))
              (1 - r (Fin.last N))
          _ <= _ := by
            exact add_le_add
              (abs_add_le (r 0 + 1) (r (Fin.last N) - r 0))
              (le_refl |1 - r (Fin.last N)|)
  have htriangle' :
      2 <= |r 0 + 1| +
          (∑ j : Fin N, |r j.succ - r j.castSucc|) +
        |1 - r (Fin.last N)| := by
    linarith
  have hscale := mul_le_mul_of_nonneg_left htriangle' (sq_nonneg m)
  nlinarith [htop, hsteps, hbottom, hscale]



theorem ginibre_chainCross_limit
    (N : Nat) (p q : Nat -> Fin (N + 1) -> Real)
    (pLim qLim : Fin (N + 1) -> Real)
    (D : Nat -> Real) (Dlim : Real)
    (hp : forall j, Tendsto (fun k => p k j) atTop (nhds (pLim j)))
    (hq : forall j, Tendsto (fun k => q k j) atTop (nhds (qLim j)))
    (hD : Tendsto D atTop (nhds Dlim))
    (hcross : forall k,
      (∑ j : Fin N,
        (p k j.castSucc * q k j.succ -
          p k j.succ * q k j.castSucc)) <= D k) :
    (∑ j : Fin N,
      (pLim j.castSucc * qLim j.succ -
        pLim j.succ * qLim j.castSucc)) <= Dlim := by
  have hsum : Tendsto
      (fun k => ∑ j : Fin N,
        (p k j.castSucc * q k j.succ -
          p k j.succ * q k j.castSucc)) atTop
      (nhds (∑ j : Fin N,
        (pLim j.castSucc * qLim j.succ -
          pLim j.succ * qLim j.castSucc))) := by
    simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
      (tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun j _ =>
        ((hp j.castSucc).mul (hq j.succ)).sub
          ((hp j.succ).mul (hq j.castSucc))))
  exact le_of_tendsto_of_tendsto hsum hD
    (Filter.Eventually.of_forall hcross)



theorem ginibre_chainCross_limit_of_plus_const
    (N : Nat) (p q : Nat -> Fin (N + 1) -> Real)
    (qLim : Fin (N + 1) -> Real) (m : Real)
    (D : Nat -> Real) (Dlim : Real)
    (hp : forall j, Tendsto (fun k => p k j) atTop (nhds m))
    (hq : forall j, Tendsto (fun k => q k j) atTop (nhds (qLim j)))
    (hD : Tendsto D atTop (nhds Dlim))
    (hcross : forall k,
      (∑ j : Fin N,
        (p k j.castSucc * q k j.succ -
          p k j.succ * q k j.castSucc)) <= D k) :
    m * (qLim (Fin.last N) - qLim 0) <= Dlim := by
  have h := ginibre_chainCross_limit N p q (fun _ => m) qLim D Dlim
    hp hq hD hcross
  have hcollapse :
      (∑ j : Fin N,
        (m * qLim j.succ - m * qLim j.castSucc)) =
        m * (qLim (Fin.last N) - qLim 0) := by
    calc
      (∑ j : Fin N,
          (m * qLim j.succ - m * qLim j.castSucc)) =
          m * ∑ j : Fin N, (qLim j.succ - qLim j.castSucc) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = m * (qLim (Fin.last N) - qLim 0) := by
        rw [sum_fin_succ_sub_castSucc]
  rw [hcollapse] at h
  exact h

end

end StatMech.Ising
