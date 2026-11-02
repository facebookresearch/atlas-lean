/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P3Domain

/-!
# A four-vertex counterexample to domain monotonicity of the support-ordered backbone weight

On the complete graph `K₄` and the subgraph `H = K₄ \ {12}`, the support-ordered direct-path weight
at edge weight `t = 2/3` is larger in `K₄` than in `H`, so domain monotonicity (P3) fails.

## i. Overview

This file works in the parity (high-temperature) form of the random-current expansion on `K₄`. An
edge configuration `A ⊆ E` contributes `t^|A|`; the vacuum mass sums over sourceless `A`, and the
direct fiber mass sums over `A` with boundary `{0, 3}` whose support-lex selected path from `0` to
`3` is the direct edge `03` (`shbK4SelectsDirect03`: `03 ∈ A` and no other `0`–`3` path of `K₄` is
supported by `A`). Their ratio `shbK4DirectRho E t` is the parity model of the backbone weight of
the direct path. At `t = 2/3` exact rational computation (`decide`) gives
`ρ_H = 54/145 < 86/225 = ρ_{K₄}`.

Headline fidelity: `shb_supportLex_edgeDomain_P3_counterexample` is proved unconditionally by
computation. It concerns the parity model only; the transfer to the real current series is in
`SupportLexParityBridge`, and to the literal backbone weight `shb_rhoSupport` in
`SupportLexK4Literal`.

## ii. Key results

- `shbK4H`, `shbK4G` : the edge sets of `K₄ \ {12}` and `K₄`
- `shbK4SelectsDirect03` : the support-lex selector picks the direct edge `03`
- `shbK4DirectRho` : the parity model of the direct-path backbone weight
- `shb_supportLex_edgeDomain_P3_counterexample` : `ρ_H(2/3) < ρ_{K₄}(2/3)` (unconditional)

## iii. Table of contents

- A. The edges of `K₄`
- B. Edge configurations and the two domains
- C. The `0`–`3` paths and the support-lex selector
- D. The fiber and vacuum masses at `t = 2/3`

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for
  Bernoulli percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745
-/
@[expose] public section

open Finset

namespace StatMech.Sharpness

/-! ## A. The edges of `K₄` -/

/-- The six edges `ij` (`i < j`) of the complete graph on `Fin 4`. -/
inductive shbK4Edge
  | e01 | e02 | e03 | e12 | e13 | e23
  deriving DecidableEq

/-- The six edges of `K₄` form a finite type. -/
instance : Fintype shbK4Edge where
  elems := {.e01, .e02, .e03, .e12, .e13, .e23}
  complete := by intro x; cases x <;> simp

namespace shbK4Edge

/-- The edge `e` is incident to the vertex `v`. -/
def Incident : shbK4Edge → Fin 4 → Prop
  | e01, v => v = 0 ∨ v = 1
  | e02, v => v = 0 ∨ v = 2
  | e03, v => v = 0 ∨ v = 3
  | e12, v => v = 1 ∨ v = 2
  | e13, v => v = 1 ∨ v = 3
  | e23, v => v = 2 ∨ v = 3

/-- Incidence is decidable. -/
instance (e : shbK4Edge) : DecidablePred e.Incident := by
  intro v
  unfold Incident
  split <;> infer_instance

end shbK4Edge

/-! ## B. Edge configurations and the two domains -/

/-- The boundary of an edge configuration `A`: the vertices of odd degree in `A`. -/
def shbK4Boundary (A : Finset shbK4Edge) : Finset (Fin 4) :=
  Finset.univ.filter fun v => Odd ((A.filter fun e => e.Incident v).card)

/-- The edge configurations supported in `E`: all subsets of `E`. -/
def shbK4Configs (E : Finset shbK4Edge) : Finset (Finset shbK4Edge) :=
  E.powerset

/-- The edge set of `K₄` with the edge `12` removed. -/
def shbK4H : Finset shbK4Edge :=
  {shbK4Edge.e01, shbK4Edge.e02, shbK4Edge.e03,
    shbK4Edge.e13, shbK4Edge.e23}

/-- The edge set of `K₄`. -/
def shbK4G : Finset shbK4Edge := Finset.univ

/-! ## C. The `0`–`3` paths and the support-lex selector -/

/-- The five simple paths from `0` to `3` in `K₄`, named by their vertex sequences. -/
inductive shbK4Path03
  | p0123 | p013 | p0213 | p023 | p03
  deriving DecidableEq

/-- The five `0`–`3` paths form a finite type. -/
instance : Fintype shbK4Path03 where
  elems := {.p0123, .p013, .p0213, .p023, .p03}
  complete := by intro x; cases x <;> simp

/-- The edge set of a `0`–`3` path. -/
def shbK4Path03.edges : shbK4Path03 → Finset shbK4Edge
  | p0123 => {shbK4Edge.e01, shbK4Edge.e12, shbK4Edge.e23}
  | p013 => {shbK4Edge.e01, shbK4Edge.e13}
  | p0213 => {shbK4Edge.e02, shbK4Edge.e12, shbK4Edge.e13}
  | p023 => {shbK4Edge.e02, shbK4Edge.e23}
  | p03 => {shbK4Edge.e03}

/-- The configuration `A` contains every edge of the path `p`. -/
def shbK4SupportsPath (A : Finset shbK4Edge) (p : shbK4Path03) : Prop :=
  p.edges ⊆ A

/-- Path support is decidable. -/
instance (A : Finset shbK4Edge) (p : shbK4Path03) :
    Decidable (shbK4SupportsPath A p) := by
  unfold shbK4SupportsPath
  infer_instance

/-- The configuration `A` has boundary `{0, 3}` and the support-lex selector picks the direct edge
`03`: `03 ∈ A` and no other `0`–`3` path is supported by `A`. -/
def shbK4SelectsDirect03 (A : Finset shbK4Edge) : Prop :=
  shbK4Boundary A = {0, 3} ∧
    shbK4Edge.e03 ∈ A ∧
    ¬ ({shbK4Edge.e01, shbK4Edge.e13} : Finset shbK4Edge) ⊆ A ∧
    ¬ ({shbK4Edge.e01, shbK4Edge.e12, shbK4Edge.e23} :
        Finset shbK4Edge) ⊆ A ∧
    ¬ ({shbK4Edge.e02, shbK4Edge.e12, shbK4Edge.e13} :
        Finset shbK4Edge) ⊆ A ∧
    ¬ ({shbK4Edge.e02, shbK4Edge.e23} : Finset shbK4Edge) ⊆ A

/-- Selection of the direct edge is decidable. -/
instance (A : Finset shbK4Edge) : Decidable (shbK4SelectsDirect03 A) := by
  unfold shbK4SelectsDirect03
  infer_instance

lemma shbK4_selectsDirect03_iff_pathEnumeration
    (A : Finset shbK4Edge) :
    shbK4SelectsDirect03 A ↔
      shbK4Boundary A = {0, 3} ∧
        shbK4SupportsPath A shbK4Path03.p03 ∧
        ∀ p, p ≠ shbK4Path03.p03 → ¬ shbK4SupportsPath A p := by
  decide +revert +kernel

/-! ## D. The fiber and vacuum masses at `t = 2/3` -/

/-- The parity-model mass `∑ t^|A|` of the configurations in `E` selecting the direct edge. -/
def shbK4DirectFiberMass (E : Finset shbK4Edge) (t : ℚ) : ℚ :=
  ∑ A ∈ shbK4Configs E, if shbK4SelectsDirect03 A then t ^ A.card else 0

/-- The parity-model mass `∑ t^|A|` of the sourceless configurations in `E`. -/
def shbK4VacuumMass (E : Finset shbK4Edge) (t : ℚ) : ℚ :=
  ∑ A ∈ shbK4Configs E, if shbK4Boundary A = ∅ then t ^ A.card else 0

/-- The parity model of the direct-path backbone weight: direct fiber mass over vacuum mass. -/
def shbK4DirectRho (E : Finset shbK4Edge) (t : ℚ) : ℚ :=
  shbK4DirectFiberMass E t / shbK4VacuumMass E t

lemma shbK4H_masses_at_two_thirds :
    shbK4DirectFiberMass shbK4H (2 / 3) = 2 / 3 ∧
      shbK4VacuumMass shbK4H (2 / 3) = 145 / 81 := by
  decide +kernel

lemma shbK4G_masses_at_two_thirds :
    shbK4DirectFiberMass shbK4G (2 / 3) = 86 / 81 ∧
      shbK4VacuumMass shbK4G (2 / 3) = 25 / 9 := by
  decide +kernel

lemma shbK4_rhos_at_two_thirds :
    shbK4DirectRho shbK4H (2 / 3) = 54 / 145 ∧
      shbK4DirectRho shbK4G (2 / 3) = 86 / 225 := by
  constructor
  · unfold shbK4DirectRho
    rw [shbK4H_masses_at_two_thirds.1, shbK4H_masses_at_two_thirds.2]
    norm_num
  · unfold shbK4DirectRho
    rw [shbK4G_masses_at_two_thirds.1, shbK4G_masses_at_two_thirds.2]
    norm_num

/-- Domain monotonicity fails for the support-ordered backbone weight in the parity model:
`ρ_{K₄ \ 12}(2/3) < ρ_{K₄}(2/3)`. -/
theorem shb_supportLex_edgeDomain_P3_counterexample :
    shbK4DirectRho shbK4H (2 / 3) < shbK4DirectRho shbK4G (2 / 3) := by
  rw [shbK4_rhos_at_two_thirds.1, shbK4_rhos_at_two_thirds.2]
  norm_num

lemma shbK4H_ssubset_shbK4G : shbK4H ⊂ shbK4G := by
  decide +kernel

end StatMech.Sharpness
