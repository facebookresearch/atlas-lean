/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Combinatorics.Graph.ArcNetwork
public import PhyslibExt.Circuits.NetworkStorageBalance

/-!
# Linear modified nodal analysis stamping

## i. Overview

Modified nodal analysis (MNA) assembles a lumped circuit into nodal
equations by stamping each branch class into blocks of a shared
incidence matrix. This module formalizes that assembly for finite
resistor, inductor, capacitor and independent voltage-source
networks on the branch-partition carrier: branches indexed by
`Fin nB` are partitioned exactly once into the four classes, branch
voltages are `Bᵀ *ᵥ v` for node potentials `v`, and branch currents
satisfy `B *ᵥ i = j` for an independently supplied nodal injection
`j`. The electrical incidence `B` is tail-positive, the negation
of the head-positive arc incidence matrix. Restricting the columns
of `B` to each class gives the capacitor, resistor, inductor and
voltage-source blocks. The stamped system couples the assembled
nodal equation `Cn *ᵥ deriv v t + G *ᵥ v t + Bl *ᵥ iL t + Bv *ᵥ iV t = j t`,
with `Cn = Bc * diagonal C * Bcᵀ` and `G = Br * diagonal (1/R) * Brᵀ`,
to the inductor equation `diagonal L *ᵥ deriv iL t - Blᵀ *ᵥ v t = 0`
and the source constraint `Bvᵀ *ᵥ v t = e`. Every resistor,
capacitor and inductor value is strictly positive on its class;
a zero-resistance branch and a prescribed-current branch are
outside the model, and a prescribed current enters only through
`j`. The ground node carries zero potential and its row is
retained. No existence or solver claim is made: an inconsistent
set of voltage sources stays inconsistent after stamping.

The equivalence between the stamped system and the branch
equations assumes differentiability of the node potentials and
of the restricted inductor current. The branch inductor law
reads the scalar derivative of each inductor current, while the
stamped equation reads the derivative of the restricted current
as one function into the branch subtype; differentiability is
what makes the two readings agree componentwise. Proofs split
nodal sums over the four disjoint branch classes, rewrite block
actions through incidence transposes, and push `deriv` through
the finite incidence combinations under those hypotheses. The
backward direction builds branch currents class by class from
the stamped data and recovers the nodal balance from the column
partition.

## ii. Key results

- `physicalIncidence_eq_neg_incidenceMatrix`: the tail-positive
  incidence is the negation of the arc incidence matrix.
- `physicalIncidence_mulVec_apply`: at a node, tail-positive
  incidence applied to branch currents is outgoing minus
  incoming current.
- `incidence_mulVec_eq_sum_restricted`: nodal current balance
  splits over the four branch classes.
- `satisfiesStampedEquations_of_satisfiesBranchEquations`:
  branch equations give the stamped equations for the restricted
  inductor and voltage-source currents.
- `exists_satisfiesBranchEquations_of_satisfiesStampedEquations`:
  stamped equations come from branch equations with the given
  restricted currents.
- `stampedEquations_iff_exists_satisfiesBranchEquations`:
  the stamped system holds exactly when branch quantities
  satisfying the branch equations exist with those restricted
  currents.
- `not_exists_satisfiesBranchEquations_of_parallel_sourceValues_ne`:
  parallel voltage sources with equal incidence columns and
  different values have no branch solution.
- `not_satisfiesStampingHypotheses_of_resistance_eq_zero`:
  a zero-resistance branch does not satisfy the stamping
  hypotheses.
- `nodalCapacitance_singleCapacitor`: a single capacitor branch
  with unit incidence stamps to nodal capacitance `3` at value `3`.

## iii. Table of contents

- A. Incidence sign adapter and column restrictions
- B. Hypotheses and the two systems
- C. Column-partition conversion
- D. Stamping equivalence and validation

## iv. References

- C. W. Ho, A. E. Ruehli, and P. A. Brennan, The modified nodal
  approach to network analysis, *IEEE Transactions on Circuits
  and Systems* 22(6), 1975, pp. 504-509: the stamped nodal
  formulation with voltage-source currents as unknowns.
- J. W. Nilsson and S. A. Riedel, *Electric Circuits*, eleventh
  edition, Pearson, 2019: branch constitutive laws, incidence
  and nodal current balance.

## A. Incidence sign adapter and column restrictions
-/

@[expose] public section

namespace PhyslibExt.Circuits.LinearMNAStamping

open Matrix PhyslibExt.Circuits.NetworkStorageBalance
  MathlibExt.Combinatorics.Graph.ArcNetwork

/-! ### A. Incidence sign adapter and column restrictions -/

/-- The tail-positive electrical incidence matrix: the negation of
the head-positive arc incidence matrix. -/
def physicalIncidence {nN nB : ℕ} (tail head : Fin nB → Fin nN) :
    Matrix (Fin nN) (Fin nB) ℝ :=
  -incidenceMatrix tail head

/-- The capacitor columns of an incidence matrix. -/
def capacitorIncidence {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Cset : Finset (Fin nB)) : Matrix (Fin nN) ↥Cset ℝ :=
  fun v e => B v (e : Fin nB)

/-- The resistor columns of an incidence matrix. -/
def resistorIncidence {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset : Finset (Fin nB)) : Matrix (Fin nN) ↥Rset ℝ :=
  fun v e => B v (e : Fin nB)

/-- The inductor columns of an incidence matrix. -/
def inductorIncidence {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Lset : Finset (Fin nB)) : Matrix (Fin nN) ↥Lset ℝ :=
  fun v e => B v (e : Fin nB)

/-- The voltage-source columns of an incidence matrix. -/
def voltageSourceIncidence {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Sset : Finset (Fin nB)) : Matrix (Fin nN) ↥Sset ℝ :=
  fun v e => B v (e : Fin nB)

/-- A branch vector restricted to one branch class. -/
def restrictVector {nB : ℕ} (s : Finset (Fin nB)) (u : Fin nB → ℝ) : ↥s → ℝ :=
  fun e => u (e : Fin nB)

/-- The nodal capacitance matrix `Bc * diagonal C * Bcᵀ`. -/
def nodalCapacitance {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Cset : Finset (Fin nB)) (Cval : Fin nB → ℝ) : Matrix (Fin nN) (Fin nN) ℝ :=
  capacitorIncidence B Cset *
    Matrix.diagonal (fun e : ↥Cset => Cval (e : Fin nB)) *
    (capacitorIncidence B Cset)ᵀ

/-- The nodal conductance matrix `Br * diagonal (1 / R) * Brᵀ`. -/
noncomputable def nodalConductance {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset : Finset (Fin nB)) (Rval : Fin nB → ℝ) : Matrix (Fin nN) (Fin nN) ℝ :=
  resistorIncidence B Rset *
    Matrix.diagonal (fun e : ↥Rset => (Rval (e : Fin nB))⁻¹) *
    (resistorIncidence B Rset)ᵀ

/-- The diagonal inductance matrix on the inductor branches. -/
def inductanceDiagonal {nB : ℕ} (Lset : Finset (Fin nB)) (Lval : Fin nB → ℝ) :
    Matrix ↥Lset ↥Lset ℝ :=
  Matrix.diagonal (fun e : ↥Lset => Lval (e : Fin nB))

/-! ### B. Hypotheses and the two systems -/

/-- The stamping hypotheses on the carrier: the classes partition
the branches exactly once and every resistor, capacitor and
inductor value is strictly positive on its class. Source branches
carry the voltage-source law in the branch equations below; no
prescribed-current branch law appears anywhere. -/
def satisfiesStampingHypotheses {nB : ℕ} (Rset Lset Cset Sset : Finset (Fin nB))
    (Rval Lval Cval : Fin nB → ℝ) : Prop :=
  IsBranchPartition nB Rset Lset Cset Sset ∧
    (∀ e : Fin nB, e ∈ Rset → 0 < Rval e) ∧
    (∀ e : Fin nB, e ∈ Cset → 0 < Cval e) ∧
    (∀ e : Fin nB, e ∈ Lset → 0 < Lval e)

/-- The carrier branch equations: zero potential at the ground
node, branch voltages from node potentials, nodal current balance
against the supplied injection, and the resistor, capacitor,
inductor and independent voltage-source element laws. -/
def satisfiesBranchEquations {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB)) (Rval Lval Cval sourceVal : Fin nB → ℝ)
    (ground : Fin nN) (j : ℝ → Fin nN → ℝ)
    (v : ℝ → Fin nN → ℝ) (vb iB : ℝ → Fin nB → ℝ) : Prop :=
  (∀ t : ℝ, v t ground = 0) ∧
    (∀ t : ℝ, vb t = Bᵀ *ᵥ v t) ∧
    (∀ t : ℝ, B *ᵥ iB t = j t) ∧
    (∀ (t : ℝ) (e : Fin nB), e ∈ Rset → vb t e = Rval e * iB t e) ∧
    (∀ (t : ℝ) (e : Fin nB), e ∈ Cset →
      iB t e = Cval e * deriv (fun s => vb s e) t) ∧
    (∀ (t : ℝ) (e : Fin nB), e ∈ Lset →
      vb t e = Lval e * deriv (fun s => iB s e) t) ∧
    (∀ (t : ℝ) (e : Fin nB), e ∈ Sset → vb t e = sourceVal e)

/-- The stamped equations: zero potential at the ground node, the
assembled nodal equation with capacitor, resistor, inductor and
voltage-source blocks, the inductor voltage equation, and the
voltage-source constraint on node potentials. -/
def satisfiesStampedEquations {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB)) (Rval Lval Cval sourceVal : Fin nB → ℝ)
    (ground : Fin nN) (j : ℝ → Fin nN → ℝ)
    (v : ℝ → Fin nN → ℝ) (iL : ℝ → ↥Lset → ℝ) (iV : ℝ → ↥Sset → ℝ) : Prop :=
  (∀ t : ℝ, v t ground = 0) ∧
    (∀ t : ℝ, nodalCapacitance B Cset Cval *ᵥ deriv v t +
        nodalConductance B Rset Rval *ᵥ v t +
        inductorIncidence B Lset *ᵥ iL t +
        voltageSourceIncidence B Sset *ᵥ iV t = j t) ∧
    (∀ t : ℝ, inductanceDiagonal Lset Lval *ᵥ deriv iL t -
        (inductorIncidence B Lset)ᵀ *ᵥ v t = 0) ∧
    (∀ t : ℝ, (voltageSourceIncidence B Sset)ᵀ *ᵥ v t =
      fun e : ↥Sset => sourceVal (e : Fin nB))

/-! ### Private proof helpers -/

private theorem restrictVector_apply {nB : ℕ} (s : Finset (Fin nB)) (u : Fin nB → ℝ)
    (e : ↥s) : restrictVector s u e = u (e : Fin nB) := rfl

private theorem sum_subtype_eq_sum_mem {nB : ℕ} (s : Finset (Fin nB)) (f : Fin nB → ℝ) :
    (∑ e : ↥s, f e) = ∑ e ∈ s, f e := by
  have h := Finset.sum_attach s f
  rwa [← Finset.univ_eq_attach] at h

private theorem diagonal_mulVec_pt {κ : Type*} [Fintype κ] [DecidableEq κ]
    (d : κ → ℝ) (z : κ → ℝ) (e : κ) :
    (Matrix.diagonal d *ᵥ z) e = d e * z e := by
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single e]
  · simp
  · intro j _ hje
    rw [ite_eq_right (fun h => hje h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ e) h

private theorem differentiableAt_pi_apply {ι : Type*} [Fintype ι] {f : ℝ → ι → ℝ}
    {t : ℝ} (h : DifferentiableAt ℝ f t) (m : ι) :
    DifferentiableAt ℝ (fun s => f s m) t := by
  have hL : DifferentiableAt ℝ
      (⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) m)) (f t) :=
    ContinuousLinearMap.differentiableAt
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) m)
  have hC := DifferentiableAt.fun_comp' (f := f) (x := t) hL h
  simpa only [ContinuousLinearMap.proj_apply] using hC

private theorem deriv_pi_apply {ι : Type*} [Fintype ι] {f : ℝ → ι → ℝ} {t : ℝ}
    (h : DifferentiableAt ℝ f t) (m : ι) : deriv (fun s => f s m) t = deriv f t m := by
  have hCLM : HasFDerivAt
      (⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) m))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) m) (f t) :=
    ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) m)
  have hC := HasFDerivAt.comp t hCLM h.hasFDerivAt
  have hD : HasDerivAt (fun s => f s m)
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) m).comp (fderiv ℝ f t)) 1) t :=
    hC.hasDerivAt
  have hderiv : deriv f t = fderiv ℝ f t 1 := rfl
  rw [hD.deriv, hderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

private theorem mulVec_deriv_apply {κ : Type*} [Fintype κ] {n : ℕ}
    (A : Matrix κ (Fin n) ℝ)
    {v : ℝ → Fin n → ℝ} {t : ℝ} (hv : DifferentiableAt ℝ v t) (i : κ) :
    (A *ᵥ deriv v t) i = deriv (fun s => (A *ᵥ v s) i) t := by
  simp only [Matrix.mulVec, dotProduct]
  rw [deriv_fun_sum (fun j _ => ((differentiableAt_pi_apply hv j).const_mul (A i j)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [deriv_const_mul _ (differentiableAt_pi_apply hv j), deriv_pi_apply hv j]

private theorem capacitorIncidence_transpose_mulVec_apply {nN nB : ℕ}
    (B : Matrix (Fin nN) (Fin nB) ℝ) (Cset : Finset (Fin nB)) (w : Fin nN → ℝ)
    (e : ↥Cset) :
    ((capacitorIncidence B Cset)ᵀ *ᵥ w) e = (Bᵀ *ᵥ w) (e : Fin nB) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, capacitorIncidence]

private theorem resistorIncidence_transpose_mulVec_apply {nN nB : ℕ}
    (B : Matrix (Fin nN) (Fin nB) ℝ) (Rset : Finset (Fin nB)) (w : Fin nN → ℝ)
    (e : ↥Rset) :
    ((resistorIncidence B Rset)ᵀ *ᵥ w) e = (Bᵀ *ᵥ w) (e : Fin nB) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, resistorIncidence]

private theorem inductorIncidence_transpose_mulVec_apply {nN nB : ℕ}
    (B : Matrix (Fin nN) (Fin nB) ℝ) (Lset : Finset (Fin nB)) (w : Fin nN → ℝ)
    (e : ↥Lset) :
    ((inductorIncidence B Lset)ᵀ *ᵥ w) e = (Bᵀ *ᵥ w) (e : Fin nB) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, inductorIncidence]

private theorem voltageSourceIncidence_transpose_mulVec_apply {nN nB : ℕ}
    (B : Matrix (Fin nN) (Fin nB) ℝ) (Sset : Finset (Fin nB)) (w : Fin nN → ℝ)
    (e : ↥Sset) :
    ((voltageSourceIncidence B Sset)ᵀ *ᵥ w) e = (Bᵀ *ᵥ w) (e : Fin nB) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, voltageSourceIncidence]

private theorem nodalCapacitance_mulVec_apply {nN nB : ℕ}
    (B : Matrix (Fin nN) (Fin nB) ℝ) (Cset : Finset (Fin nB)) (Cval : Fin nB → ℝ)
    (w : Fin nN → ℝ) (n : Fin nN) :
    (nodalCapacitance B Cset Cval *ᵥ w) n =
      ∑ e : ↥Cset, B n e * (Cval e * ((capacitorIncidence B Cset)ᵀ *ᵥ w) e) := by
  have hD : (Matrix.diagonal (fun e : ↥Cset => Cval (e : Fin nB)) *ᵥ
      ((capacitorIncidence B Cset)ᵀ *ᵥ w)) =
      (fun e : ↥Cset => Cval (e : Fin nB) * ((capacitorIncidence B Cset)ᵀ *ᵥ w) e) :=
    funext (fun e => diagonal_mulVec_pt _ _ e)
  simp only [nodalCapacitance]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hD]
  simp only [Matrix.mulVec, dotProduct, capacitorIncidence]

private theorem nodalConductance_mulVec_apply {nN nB : ℕ}
    (B : Matrix (Fin nN) (Fin nB) ℝ) (Rset : Finset (Fin nB)) (Rval : Fin nB → ℝ)
    (w : Fin nN → ℝ) (n : Fin nN) :
    (nodalConductance B Rset Rval *ᵥ w) n =
      ∑ e : ↥Rset, B n e * ((Rval e)⁻¹ * ((resistorIncidence B Rset)ᵀ *ᵥ w) e) := by
  have hD : (Matrix.diagonal (fun e : ↥Rset => (Rval (e : Fin nB))⁻¹) *ᵥ
      ((resistorIncidence B Rset)ᵀ *ᵥ w)) =
      (fun e : ↥Rset => (Rval (e : Fin nB))⁻¹ * ((resistorIncidence B Rset)ᵀ *ᵥ w) e) :=
    funext (fun e => diagonal_mulVec_pt _ _ e)
  simp only [nodalConductance]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hD]
  simp only [Matrix.mulVec, dotProduct, resistorIncidence]

private theorem inductanceDiagonal_mulVec_apply {nB : ℕ}
    (Lset : Finset (Fin nB)) (Lval : Fin nB → ℝ) (z : ↥Lset → ℝ) (e : ↥Lset) :
    (inductanceDiagonal Lset Lval *ᵥ z) e = Lval e * z e := by
  simp only [inductanceDiagonal]
  exact diagonal_mulVec_pt _ _ e

/-! ### C. Column-partition conversion -/

/-- The electrical incidence matrix is the negation of the arc
incidence matrix, by definition of the sign adapter. -/
lemma physicalIncidence_eq_neg_incidenceMatrix {nN nB : ℕ}
    (tail head : Fin nB → Fin nN) :
    physicalIncidence tail head = -incidenceMatrix tail head := by
  rfl

/-- At a node, tail-positive incidence applied to branch currents
is outgoing current minus incoming current. -/
lemma physicalIncidence_mulVec_apply {nN nB : ℕ}
    (tail head : Fin nB → Fin nN) (iB : Fin nB → ℝ) (vnode : Fin nN) :
    (physicalIncidence tail head *ᵥ iB) vnode =
      (∑ e ∈ (Finset.univ : Finset (Fin nB)).filter (fun e => tail e = vnode), iB e) -
        ∑ e ∈ (Finset.univ : Finset (Fin nB)).filter (fun e => head e = vnode), iB e := by
  have hterm : ∀ e : Fin nB, (physicalIncidence tail head) vnode e * iB e =
      (if tail e = vnode then iB e else 0) - (if head e = vnode then iB e else 0) := by
    intro e
    show (-(((if head e = vnode then (1 : ℝ) else 0) - (if tail e = vnode then 1 else 0)))) *
        iB e = _
    split_ifs <;> simp_all
  have htail : (∑ e ∈ (Finset.univ : Finset (Fin nB)).filter (fun e => tail e = vnode), iB e)
      = ∑ e, (if tail e = vnode then iB e else 0) := Finset.sum_filter _ _
  have hhead : (∑ e ∈ (Finset.univ : Finset (Fin nB)).filter (fun e => head e = vnode), iB e)
      = ∑ e, (if head e = vnode then iB e else 0) := Finset.sum_filter _ _
  calc (physicalIncidence tail head *ᵥ iB) vnode
      = ∑ e, (physicalIncidence tail head) vnode e * iB e := by
        simp only [Matrix.mulVec, dotProduct]
    _ = ∑ e, ((if tail e = vnode then iB e else 0) - (if head e = vnode then iB e else 0)) :=
        Finset.sum_congr rfl (fun e _ => hterm e)
    _ = (∑ e, (if tail e = vnode then iB e else 0)) - ∑ e, (if head e = vnode then iB e else 0) :=
        Finset.sum_sub_distrib _ _
    _ = _ := by rw [htail, hhead]

/-- **Column partition of nodal current balance.** Applied to a
branch current vector, the full incidence matrix splits as the sum
of its four class blocks applied to the restricted currents. -/
lemma incidence_mulVec_eq_sum_restricted {nN nB : ℕ}
    (B : Matrix (Fin nN) (Fin nB) ℝ) (Rset Lset Cset Sset : Finset (Fin nB))
    (hpart : IsBranchPartition nB Rset Lset Cset Sset) (iB : Fin nB → ℝ) :
    B *ᵥ iB = capacitorIncidence B Cset *ᵥ restrictVector Cset iB +
      resistorIncidence B Rset *ᵥ restrictVector Rset iB +
      inductorIncidence B Lset *ᵥ restrictVector Lset iB +
      voltageSourceIncidence B Sset *ᵥ restrictVector Sset iB := by
  have hpart' : Disjoint Rset Lset ∧ Disjoint Rset Cset ∧ Disjoint Rset Sset ∧
      Disjoint Lset Cset ∧ Disjoint Lset Sset ∧ Disjoint Cset Sset ∧
      Rset ∪ Lset ∪ Cset ∪ Sset = Finset.univ := hpart
  obtain ⟨hRL, hRC, hRS, hLC, hLS, hCS, hunion⟩ := hpart'
  have hC : ∀ n : Fin nN, (capacitorIncidence B Cset *ᵥ restrictVector Cset iB) n =
      ∑ e ∈ Cset, B n e * iB e := by
    intro n
    simp only [Matrix.mulVec, dotProduct, capacitorIncidence, restrictVector]
    exact sum_subtype_eq_sum_mem Cset (fun e' => B n e' * iB e')
  have hR : ∀ n : Fin nN, (resistorIncidence B Rset *ᵥ restrictVector Rset iB) n =
      ∑ e ∈ Rset, B n e * iB e := by
    intro n
    simp only [Matrix.mulVec, dotProduct, resistorIncidence, restrictVector]
    exact sum_subtype_eq_sum_mem Rset (fun e' => B n e' * iB e')
  have hL : ∀ n : Fin nN, (inductorIncidence B Lset *ᵥ restrictVector Lset iB) n =
      ∑ e ∈ Lset, B n e * iB e := by
    intro n
    simp only [Matrix.mulVec, dotProduct, inductorIncidence, restrictVector]
    exact sum_subtype_eq_sum_mem Lset (fun e' => B n e' * iB e')
  have hS : ∀ n : Fin nN, (voltageSourceIncidence B Sset *ᵥ restrictVector Sset iB) n =
      ∑ e ∈ Sset, B n e * iB e := by
    intro n
    simp only [Matrix.mulVec, dotProduct, voltageSourceIncidence, restrictVector]
    exact sum_subtype_eq_sum_mem Sset (fun e' => B n e' * iB e')
  have dRLC : Disjoint (Rset ∪ Lset) Cset :=
    Finset.disjoint_union_left.mpr ⟨hRC, hLC⟩
  have dRLCS : Disjoint (Rset ∪ Lset ∪ Cset) Sset :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hRS, hLS⟩, hCS⟩
  funext n
  simp only [Pi.add_apply]
  rw [hC n, hR n, hL n, hS n]
  simp only [Matrix.mulVec, dotProduct]
  rw [← hunion, Finset.sum_union dRLCS, Finset.sum_union dRLC, Finset.sum_union hRL]
  ac_rfl

/-! ### D. Stamping equivalence and validation -/

/-- Forward stamping: branch equations with differentiable node
potentials give the stamped equations for the restricted inductor
and voltage-source currents. -/
theorem satisfiesStampedEquations_of_satisfiesBranchEquations
    {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB)) (Rval Lval Cval sourceVal : Fin nB → ℝ)
    (ground : Fin nN) (j : ℝ → Fin nN → ℝ)
    (v : ℝ → Fin nN → ℝ) (vb iB : ℝ → Fin nB → ℝ)
    (hhyp : satisfiesStampingHypotheses Rset Lset Cset Sset Rval Lval Cval)
    (hv : Differentiable ℝ v)
    (hiL : Differentiable ℝ (fun t => restrictVector Lset (iB t)))
    (h : satisfiesBranchEquations B Rset Lset Cset Sset Rval Lval Cval sourceVal
      ground j v vb iB) :
    satisfiesStampedEquations B Rset Lset Cset Sset Rval Lval Cval sourceVal
      ground j v (fun t => restrictVector Lset (iB t))
      (fun t => restrictVector Sset (iB t)) := by
  have hhyp' : IsBranchPartition nB Rset Lset Cset Sset ∧
      (∀ e : Fin nB, e ∈ Rset → 0 < Rval e) ∧
      (∀ e : Fin nB, e ∈ Cset → 0 < Cval e) ∧
      (∀ e : Fin nB, e ∈ Lset → 0 < Lval e) := hhyp
  obtain ⟨hpart, hRpos, _, _⟩ := hhyp'
  have h' : (∀ t : ℝ, v t ground = 0) ∧
      (∀ t : ℝ, vb t = Bᵀ *ᵥ v t) ∧
      (∀ t : ℝ, B *ᵥ iB t = j t) ∧
      (∀ (t : ℝ) (e : Fin nB), e ∈ Rset → vb t e = Rval e * iB t e) ∧
      (∀ (t : ℝ) (e : Fin nB), e ∈ Cset →
        iB t e = Cval e * deriv (fun s => vb s e) t) ∧
      (∀ (t : ℝ) (e : Fin nB), e ∈ Lset →
        vb t e = Lval e * deriv (fun s => iB s e) t) ∧
      (∀ (t : ℝ) (e : Fin nB), e ∈ Sset → vb t e = sourceVal e) := h
  obtain ⟨hground, hvb, hkcl, hR, hC, hL, hS⟩ := h'
  have hCblk : ∀ t : ℝ, nodalCapacitance B Cset Cval *ᵥ deriv v t =
      capacitorIncidence B Cset *ᵥ restrictVector Cset (iB t) := by
    intro t
    funext n
    have hRHS : (capacitorIncidence B Cset *ᵥ restrictVector Cset (iB t)) n =
        ∑ e : ↥Cset, B n e * iB t e := by
      simp only [Matrix.mulVec, dotProduct, capacitorIncidence, restrictVector]
    rw [nodalCapacitance_mulVec_apply, hRHS]
    apply Finset.sum_congr rfl
    intro e _
    have hBc : ((capacitorIncidence B Cset)ᵀ *ᵥ deriv v t) e =
        deriv (fun s => vb s (e : Fin nB)) t := by
      have h1 := mulVec_deriv_apply ((capacitorIncidence B Cset)ᵀ) (hv t) e
      have h2 : (fun s => ((capacitorIncidence B Cset)ᵀ *ᵥ v s) e) =
          (fun s => vb s (e : Fin nB)) := by
        funext s
        rw [capacitorIncidence_transpose_mulVec_apply]
        exact (congrFun (hvb s) (e : Fin nB)).symm
      rw [h1, h2]
    have hCe := hC t (e : Fin nB) e.property
    rw [hBc, ← hCe]
  have hRblk : ∀ t : ℝ, nodalConductance B Rset Rval *ᵥ v t =
      resistorIncidence B Rset *ᵥ restrictVector Rset (iB t) := by
    intro t
    funext n
    have hRHS : (resistorIncidence B Rset *ᵥ restrictVector Rset (iB t)) n =
        ∑ e : ↥Rset, B n e * iB t e := by
      simp only [Matrix.mulVec, dotProduct, resistorIncidence, restrictVector]
    rw [nodalConductance_mulVec_apply, hRHS]
    apply Finset.sum_congr rfl
    intro e _
    have hBr : ((resistorIncidence B Rset)ᵀ *ᵥ v t) e = vb t (e : Fin nB) := by
      rw [resistorIncidence_transpose_mulVec_apply]
      exact (congrFun (hvb t) (e : Fin nB)).symm
    have hRe := hR t (e : Fin nB) e.property
    have hne : Rval (e : Fin nB) ≠ 0 := ne_of_gt (hRpos _ e.property)
    rw [hBr, hRe]
    congr 1
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hnodal : ∀ t : ℝ, nodalCapacitance B Cset Cval *ᵥ deriv v t +
        nodalConductance B Rset Rval *ᵥ v t +
        inductorIncidence B Lset *ᵥ (fun t => restrictVector Lset (iB t)) t +
        voltageSourceIncidence B Sset *ᵥ (fun t => restrictVector Sset (iB t)) t = j t := by
    intro t
    have hpart_sum :=
      incidence_mulVec_eq_sum_restricted B Rset Lset Cset Sset hpart (iB t)
    rw [hCblk t, hRblk t]
    show capacitorIncidence B Cset *ᵥ restrictVector Cset (iB t) +
        resistorIncidence B Rset *ᵥ restrictVector Rset (iB t) +
        inductorIncidence B Lset *ᵥ restrictVector Lset (iB t) +
        voltageSourceIncidence B Sset *ᵥ restrictVector Sset (iB t) = j t
    rw [← hpart_sum, hkcl t]
  have hind : ∀ t : ℝ, inductanceDiagonal Lset Lval *ᵥ
        deriv (fun t => restrictVector Lset (iB t)) t -
        (inductorIncidence B Lset)ᵀ *ᵥ v t = 0 := by
    intro t
    funext e
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [inductanceDiagonal_mulVec_apply]
    have hfun : (fun s => (fun t => restrictVector Lset (iB t)) s e) =
        (fun s => iB s (e : Fin nB)) := rfl
    have h1 := deriv_pi_apply (hiL t) (m := e)
    rw [hfun] at h1
    rw [← h1]
    have hBl : ((inductorIncidence B Lset)ᵀ *ᵥ v t) e = vb t (e : Fin nB) := by
      rw [inductorIncidence_transpose_mulVec_apply]
      exact (congrFun (hvb t) (e : Fin nB)).symm
    have hLe := hL t (e : Fin nB) e.property
    rw [hBl, hLe]
    exact sub_self _
  have hsrc : ∀ t : ℝ, (voltageSourceIncidence B Sset)ᵀ *ᵥ v t =
      fun e : ↥Sset => sourceVal (e : Fin nB) := by
    intro t
    funext e
    show ((voltageSourceIncidence B Sset)ᵀ *ᵥ v t) e = sourceVal (e : Fin nB)
    rw [voltageSourceIncidence_transpose_mulVec_apply]
    have hb : (Bᵀ *ᵥ v t) (e : Fin nB) = vb t (e : Fin nB) :=
      (congrFun (hvb t) _).symm
    have hSe := hS t (e : Fin nB) e.property
    rw [hb, hSe]
  exact ⟨hground, hnodal, hind, hsrc⟩

/-- Backward assembly: stamped equations with differentiable node
potentials come from branch voltages and branch currents satisfying
the carrier equations, with the prescribed restricted currents. -/
theorem exists_satisfiesBranchEquations_of_satisfiesStampedEquations
    {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB)) (Rval Lval Cval sourceVal : Fin nB → ℝ)
    (ground : Fin nN) (j : ℝ → Fin nN → ℝ)
    (v : ℝ → Fin nN → ℝ) (iL : ℝ → ↥Lset → ℝ) (iV : ℝ → ↥Sset → ℝ)
    (hhyp : satisfiesStampingHypotheses Rset Lset Cset Sset Rval Lval Cval)
    (hv : Differentiable ℝ v)
    (hiL : Differentiable ℝ iL)
    (h : satisfiesStampedEquations B Rset Lset Cset Sset Rval Lval Cval sourceVal
      ground j v iL iV) :
    ∃ (vb iB : ℝ → Fin nB → ℝ),
      satisfiesBranchEquations B Rset Lset Cset Sset Rval Lval Cval sourceVal
        ground j v vb iB ∧
        (∀ t : ℝ, restrictVector Lset (iB t) = iL t) ∧
        (∀ t : ℝ, restrictVector Sset (iB t) = iV t) := by
  have hhyp' : IsBranchPartition nB Rset Lset Cset Sset ∧
      (∀ e : Fin nB, e ∈ Rset → 0 < Rval e) ∧
      (∀ e : Fin nB, e ∈ Cset → 0 < Cval e) ∧
      (∀ e : Fin nB, e ∈ Lset → 0 < Lval e) := hhyp
  obtain ⟨hpart, hRpos, _, _⟩ := hhyp'
  have hpart' : Disjoint Rset Lset ∧ Disjoint Rset Cset ∧ Disjoint Rset Sset ∧
      Disjoint Lset Cset ∧ Disjoint Lset Sset ∧ Disjoint Cset Sset ∧
      Rset ∪ Lset ∪ Cset ∪ Sset = Finset.univ := hpart
  obtain ⟨hRL, hRC, hRS, hLC, hLS, hCS, _⟩ := hpart'
  have h' : (∀ t : ℝ, v t ground = 0) ∧
      (∀ t : ℝ, nodalCapacitance B Cset Cval *ᵥ deriv v t +
        nodalConductance B Rset Rval *ᵥ v t +
        inductorIncidence B Lset *ᵥ iL t +
        voltageSourceIncidence B Sset *ᵥ iV t = j t) ∧
      (∀ t : ℝ, inductanceDiagonal Lset Lval *ᵥ deriv iL t -
        (inductorIncidence B Lset)ᵀ *ᵥ v t = 0) ∧
      (∀ t : ℝ, (voltageSourceIncidence B Sset)ᵀ *ᵥ v t =
        fun e : ↥Sset => sourceVal (e : Fin nB)) := h
  obtain ⟨hground, hnodal, hind, hsrc⟩ := h'
  have notR_of_C : ∀ e : Fin nB, e ∈ Cset → e ∉ Rset := by
    intro e heC heR
    exact (Finset.disjoint_left.mp hRC) heR heC
  have notR_of_L : ∀ e : Fin nB, e ∈ Lset → e ∉ Rset := by
    intro e heL heR
    exact (Finset.disjoint_left.mp hRL) heR heL
  have notC_of_L : ∀ e : Fin nB, e ∈ Lset → e ∉ Cset := by
    intro e heL heC
    exact (Finset.disjoint_left.mp hLC) heL heC
  have notR_of_S : ∀ e : Fin nB, e ∈ Sset → e ∉ Rset := by
    intro e heS heR
    exact (Finset.disjoint_left.mp hRS) heR heS
  have notC_of_S : ∀ e : Fin nB, e ∈ Sset → e ∉ Cset := by
    intro e heS heC
    exact (Finset.disjoint_left.mp hCS) heC heS
  have notL_of_S : ∀ e : Fin nB, e ∈ Sset → e ∉ Lset := by
    intro e heS heL
    exact (Finset.disjoint_left.mp hLS) heL heS
  set vb : ℝ → Fin nB → ℝ := (fun t => Bᵀ *ᵥ v t) with hvb_def
  set iB : ℝ → Fin nB → ℝ := (fun t e =>
    if hRe : e ∈ Rset then (Bᵀ *ᵥ v t) e / Rval e
    else if hCe : e ∈ Cset then Cval e * deriv (fun s => (Bᵀ *ᵥ v s) e) t
    else if hLe : e ∈ Lset then iL t ⟨e, hLe⟩
    else if hSe : e ∈ Sset then iV t ⟨e, hSe⟩
    else 0) with hiB_def
  have hiB_R : ∀ (t : ℝ) (e : Fin nB) (he : e ∈ Rset),
      iB t e = (Bᵀ *ᵥ v t) e / Rval e := by
    intro t e he
    simp only [hiB_def]
    rw [dite_eq_left he]
  have hiB_C : ∀ (t : ℝ) (e : Fin nB) (he : e ∈ Cset),
      iB t e = Cval e * deriv (fun s => (Bᵀ *ᵥ v s) e) t := by
    intro t e he
    have heR : e ∉ Rset := notR_of_C e he
    simp only [hiB_def]
    rw [dite_eq_right heR, dite_eq_left he]
  have hiB_L : ∀ (t : ℝ) (e : Fin nB) (he : e ∈ Lset),
      iB t e = iL t ⟨e, he⟩ := by
    intro t e he
    have heR : e ∉ Rset := notR_of_L e he
    have heC : e ∉ Cset := notC_of_L e he
    simp only [hiB_def]
    rw [dite_eq_right heR, dite_eq_right heC, dite_eq_left he]
  have hiB_S : ∀ (t : ℝ) (e : Fin nB) (he : e ∈ Sset),
      iB t e = iV t ⟨e, he⟩ := by
    intro t e he
    have heR : e ∉ Rset := notR_of_S e he
    have heC : e ∉ Cset := notC_of_S e he
    have heL : e ∉ Lset := notL_of_S e he
    simp only [hiB_def]
    rw [dite_eq_right heR, dite_eq_right heC, dite_eq_right heL, dite_eq_left he]
  have hresL : ∀ t : ℝ, restrictVector Lset (iB t) = iL t := by
    intro t
    funext e
    show iB t (e : Fin nB) = iL t e
    rw [hiB_L t _ e.property]
  have hresS : ∀ t : ℝ, restrictVector Sset (iB t) = iV t := by
    intro t
    funext e
    show iB t (e : Fin nB) = iV t e
    rw [hiB_S t _ e.property]
  have hvb_eq : ∀ t : ℝ, vb t = Bᵀ *ᵥ v t := fun t => congrFun hvb_def t
  have hBR : ∀ (t : ℝ) (e : Fin nB), e ∈ Rset → vb t e = Rval e * iB t e := by
    intro t e he
    have hne : Rval e ≠ 0 := ne_of_gt (hRpos e he)
    rw [hiB_R t e he]
    have hvbe : vb t e = (Bᵀ *ᵥ v t) e := congrFun (hvb_eq t) e
    rw [hvbe, div_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have hBC : ∀ (t : ℝ) (e : Fin nB), e ∈ Cset →
      iB t e = Cval e * deriv (fun s => vb s e) t := by
    intro t e he
    have hfun : (fun s => (Bᵀ *ᵥ v s) e) = (fun s => vb s e) := by
      funext s
      exact (congrFun (hvb_eq s) e).symm
    rw [hiB_C t e he, hfun]
  have hBL : ∀ (t : ℝ) (e : Fin nB), e ∈ Lset →
      vb t e = Lval e * deriv (fun s => iB s e) t := by
    intro t e he
    have hfun : (fun s => iB s e) = (fun s => iL s ⟨e, he⟩) :=
      funext (fun s => hiB_L s e he)
    have hderiv : deriv (fun s => iB s e) t = deriv iL t ⟨e, he⟩ := by
      rw [hfun]
      exact deriv_pi_apply (hiL t) ⟨e, he⟩
    rw [hderiv]
    have hBl : ((inductorIncidence B Lset)ᵀ *ᵥ v t) ⟨e, he⟩ = vb t e := by
      rw [inductorIncidence_transpose_mulVec_apply]
    have hindt := congrFun (hind t) (⟨e, he⟩ : ↥Lset)
    simp only [Pi.sub_apply, Pi.zero_apply] at hindt
    rw [inductanceDiagonal_mulVec_apply, hBl] at hindt
    exact (eq_of_sub_eq_zero hindt).symm
  have hBS : ∀ (t : ℝ) (e : Fin nB), e ∈ Sset → vb t e = sourceVal e := by
    intro t e he
    have hBv : ((voltageSourceIncidence B Sset)ᵀ *ᵥ v t) ⟨e, he⟩ = vb t e := by
      rw [voltageSourceIncidence_transpose_mulVec_apply]
    have hsrct := congrFun (hsrc t) (⟨e, he⟩ : ↥Sset)
    rw [hBv] at hsrct
    exact hsrct
  have hkcl' : ∀ t : ℝ, B *ᵥ iB t = j t := by
    intro t
    have hpart_sum :=
      incidence_mulVec_eq_sum_restricted B Rset Lset Cset Sset hpart (iB t)
    have hCblk : capacitorIncidence B Cset *ᵥ restrictVector Cset (iB t) =
        nodalCapacitance B Cset Cval *ᵥ deriv v t := by
      funext n
      have hRHS : (capacitorIncidence B Cset *ᵥ restrictVector Cset (iB t)) n =
          ∑ e : ↥Cset, B n e * iB t e := by
        simp only [Matrix.mulVec, dotProduct, capacitorIncidence, restrictVector]
      rw [hRHS, nodalCapacitance_mulVec_apply]
      apply Finset.sum_congr rfl
      intro e _
      have hCe := hiB_C t (e : Fin nB) e.property
      have hBc : ((capacitorIncidence B Cset)ᵀ *ᵥ deriv v t) e =
          deriv (fun s => (Bᵀ *ᵥ v s) (e : Fin nB)) t := by
        have h1 := mulVec_deriv_apply ((capacitorIncidence B Cset)ᵀ) (hv t) e
        have h2 : (fun s => ((capacitorIncidence B Cset)ᵀ *ᵥ v s) e) =
            (fun s => (Bᵀ *ᵥ v s) (e : Fin nB)) := by
          funext s
          exact capacitorIncidence_transpose_mulVec_apply B Cset (v s) e
        rw [h1, h2]
      rw [hCe, hBc]
    have hRblk : resistorIncidence B Rset *ᵥ restrictVector Rset (iB t) =
        nodalConductance B Rset Rval *ᵥ v t := by
      funext n
      have hRHS : (resistorIncidence B Rset *ᵥ restrictVector Rset (iB t)) n =
          ∑ e : ↥Rset, B n e * iB t e := by
        simp only [Matrix.mulVec, dotProduct, resistorIncidence, restrictVector]
      rw [hRHS, nodalConductance_mulVec_apply]
      apply Finset.sum_congr rfl
      intro e _
      have hRe := hiB_R t (e : Fin nB) e.property
      have hBr : ((resistorIncidence B Rset)ᵀ *ᵥ v t) e = (Bᵀ *ᵥ v t) (e : Fin nB) :=
        resistorIncidence_transpose_mulVec_apply B Rset (v t) e
      rw [hRe, hBr]
      congr 1
      rw [div_eq_inv_mul]
    have hLblk : inductorIncidence B Lset *ᵥ restrictVector Lset (iB t) =
        inductorIncidence B Lset *ᵥ iL t := by
      rw [hresL t]
    have hSblk : voltageSourceIncidence B Sset *ᵥ restrictVector Sset (iB t) =
        voltageSourceIncidence B Sset *ᵥ iV t := by
      rw [hresS t]
    rw [hpart_sum, hCblk, hRblk, hLblk, hSblk]
    exact hnodal t
  refine ⟨vb, iB, ?_, hresL, hresS⟩
  exact ⟨hground, hvb_eq, hkcl', hBR, hBC, hBL, hBS⟩

/-- **Stamping correctness.** Under the stamping hypotheses, with
differentiable node potentials, the stamped equations hold for
given inductor and voltage-source currents if and only if branch
voltages and branch currents satisfying the carrier equations exist
with those restricted currents. -/
theorem stampedEquations_iff_exists_satisfiesBranchEquations
    {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB)) (Rval Lval Cval sourceVal : Fin nB → ℝ)
    (ground : Fin nN) (j : ℝ → Fin nN → ℝ)
    (v : ℝ → Fin nN → ℝ) (iL : ℝ → ↥Lset → ℝ) (iV : ℝ → ↥Sset → ℝ)
    (hhyp : satisfiesStampingHypotheses Rset Lset Cset Sset Rval Lval Cval)
    (hv : Differentiable ℝ v)
    (hiL : Differentiable ℝ iL) :
    satisfiesStampedEquations B Rset Lset Cset Sset Rval Lval Cval sourceVal
        ground j v iL iV ↔
      ∃ (vb iB : ℝ → Fin nB → ℝ),
        satisfiesBranchEquations B Rset Lset Cset Sset Rval Lval Cval sourceVal
          ground j v vb iB ∧
          (∀ t : ℝ, restrictVector Lset (iB t) = iL t) ∧
          (∀ t : ℝ, restrictVector Sset (iB t) = iV t) := by
  constructor
  · intro h
    exact exists_satisfiesBranchEquations_of_satisfiesStampedEquations
      B Rset Lset Cset Sset Rval Lval Cval sourceVal ground j v iL iV hhyp hv hiL h
  · rintro ⟨vb, iB, hbr, hresL, hresS⟩
    have eL : (fun t => restrictVector Lset (iB t)) = iL := funext hresL
    have eS : (fun t => restrictVector Sset (iB t)) = iV := funext hresS
    have hiL' : Differentiable ℝ (fun t => restrictVector Lset (iB t)) := by
      rw [eL]
      exact hiL
    have hfwd := satisfiesStampedEquations_of_satisfiesBranchEquations
      B Rset Lset Cset Sset Rval Lval Cval sourceVal ground j v vb iB hhyp hv hiL' hbr
    rw [eL, eS] at hfwd
    exact hfwd

/-! ### D. Stamping equivalence and validation (continued) -/

/-- Parallel voltage-source branches with the same incidence column
and different source values have no branch solution at all:
stamping does not create a solver for an inconsistent source set. -/
lemma not_exists_satisfiesBranchEquations_of_parallel_sourceValues_ne
    {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB)) (Rval Lval Cval sourceVal : Fin nB → ℝ)
    (ground : Fin nN) (j : ℝ → Fin nN → ℝ) (v : ℝ → Fin nN → ℝ)
    (e₁ e₂ : Fin nB) (he₁ : e₁ ∈ Sset) (he₂ : e₂ ∈ Sset)
    (hcol : ∀ vnode : Fin nN, B vnode e₁ = B vnode e₂)
    (hne : sourceVal e₁ ≠ sourceVal e₂) :
    ¬ ∃ (vb iB : ℝ → Fin nB → ℝ),
      satisfiesBranchEquations B Rset Lset Cset Sset Rval Lval Cval sourceVal
        ground j v vb iB := by
  rintro ⟨vb, iB, hground, hvb, hkcl, hR, hC, hL, hS⟩
  have hs1 := hS 0 e₁ he₁
  have hs2 := hS 0 e₂ he₂
  have hb := hvb 0
  have c1 : vb 0 e₁ = (Bᵀ *ᵥ v 0) e₁ := congrFun hb e₁
  have c2 : vb 0 e₂ = (Bᵀ *ᵥ v 0) e₂ := congrFun hb e₂
  have hcol' : (Bᵀ *ᵥ v 0) e₁ = (Bᵀ *ᵥ v 0) e₂ := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro n _
    rw [hcol n]
  have e12 : vb 0 e₁ = vb 0 e₂ := by rw [c1, c2, hcol']
  rw [hs1, hs2] at e12
  exact hne e12

/-- A zero-resistance branch is outside the stamping hypotheses:
it is excluded by the strict positivity clause, not filtered out
of the network. -/
lemma not_satisfiesStampingHypotheses_of_resistance_eq_zero
    {nB : ℕ} (Rset Lset Cset Sset : Finset (Fin nB))
    (Rval Lval Cval : Fin nB → ℝ) (e : Fin nB) (he : e ∈ Rset) (hR : Rval e = 0) :
    ¬ satisfiesStampingHypotheses Rset Lset Cset Sset Rval Lval Cval := by
  intro h
  obtain ⟨_, hRpos, _, _⟩ := h
  have hlt := hRpos e he
  rw [hR] at hlt
  exact absurd hlt (lt_irrefl 0)

/-- A single capacitor branch on a single node with unit incidence
stamps to the scalar nodal capacitance `3` for capacitance value
`3`. -/
lemma nodalCapacitance_singleCapacitor :
    nodalCapacitance (1 : Matrix (Fin 1) (Fin 1) ℝ) {0} (fun _ => 3) =
      !![(3 : ℝ)] := by
  have hcollapse : ∀ f : ↥(({0} : Finset (Fin 1))) → ℝ,
      (∑ k, f k) = f ⟨0, Finset.mem_singleton_self 0⟩ := by
    intro f
    refine Finset.sum_eq_single _ ?_ ?_
    · intro b _ hb
      exfalso
      apply hb
      exact Subtype.ext (Finset.mem_singleton.mp b.property)
    · intro h
      exact absurd (Finset.mem_univ _) h
  ext i j
  rw [Fin.eq_zero i, Fin.eq_zero j]
  simp only [nodalCapacitance, Matrix.mul_apply, hcollapse, capacitorIncidence,
    Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.one_apply,
    ite_true, Matrix.of_apply, Matrix.cons_val_zero]
  norm_num

end PhyslibExt.Circuits.LinearMNAStamping
