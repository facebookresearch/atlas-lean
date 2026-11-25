/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_SemistableCharts.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.LPolynomial
public import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluation

/-!
# Component charts and annuli of a semistable reduction

Let `A` be a valuation subring of a field `L` and `F / L` a function field. A semistable model
of the curve over `A` is described by charts and annuli:

* `AlgebraicCurve.ComponentChart A F Fbar` records one irreducible component of the special
  fibre, with function field `Fbar` over the residue field of `A`: a valuation subring of `F`
  reducing onto `Fbar`, the places of `F` whose reduction lands in that component away from the
  nodes, and the compatibility of reduction with evaluation and with divisors.
* `AlgebraicCurve.Annulus A F` records an open annulus `{P : π ≺ z(P) ≺ 1}` of rational places,
  with coordinate `param`, modulus `π`, the order-one property of `z - z(P)`, and the unit
  principle on the annulus.
* `AlgebraicCurve.Annulus.IsAttached An C x` says that the annulus `An` abuts the component of
  `C` at the node `x`, with the coordinate reducing to a uniformizer at `x` and absolute values
  of units on the annulus governed by their order at `x`.
-/

@[expose] public section

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

/-- A chart on one component of the special fibre of a model of `F` over the valuation subring
`A`, with function field `Fbar` over the residue field of `A`. -/
structure ComponentChart where
  /-- The valuation subring of `F` attached to the generic point of the component. -/
  integers : ValuationSubring F
  /-- Reduction of functions onto the function field of the component. -/
  residue : integers →+* Fbar
  /-- The places of `F` whose reduction lies in this component. -/
  dom : Set (Place L F)
  /-- The nodes of the special fibre lying on this component. -/
  nodes : Finset (Place (IsLocalRing.ResidueField A) Fbar)
  /-- The reduction map on places. -/
  placeMap : Place L F → Place (IsLocalRing.ResidueField A) Fbar
  /-- A constant is integral for the component exactly when it lies in `A`. -/
  algebraMap_mem_iff : ∀ x : L, algebraMap L F x ∈ integers ↔ x ∈ A
  /-- Reduction is surjective. -/
  residue_surjective : Function.Surjective residue
  /-- The kernel of reduction is the maximal ideal of `integers`. -/
  ker_residue : RingHom.ker residue = maximalIdeal integers
  /-- Reduction of constants is reduction modulo the maximal ideal of `A`. -/
  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a)
  /-- Every nonzero function can be rescaled by a constant to have nonzero reduction. -/
  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers, residue ⟨c • f, h⟩ ≠ 0
  /-- Places of the chart reduce away from the nodes. -/
  placeMap_not_mem_nodes : ∀ P ∈ dom, placeMap P ∉ nodes
  /-- Reduction commutes with evaluation at rational places of the chart, for functions regular
  on the whole fibre over the reduced point. -/
  pointwise : ∀ P ∈ dom, P.IsRational → ∀ (f : F) (hf : f ∈ integers),
    (∀ w ∈ dom, placeMap w = placeMap P → f ∈ w.toValuationSubring) →
      ∃ (hm : (residue ⟨f, hf⟩ : Fbar) ∈ (placeMap P).toValuationSubring)
        (h : P.evalAt f ∈ A),
        algebraMap (IsLocalRing.ResidueField A) (placeMap P).ResidueField
            (IsLocalRing.residue A ⟨P.evalAt f, h⟩)
          = IsLocalRing.residue (placeMap P).toValuationSubring ⟨residue ⟨f, hf⟩, hm⟩
  /-- Away from the nodes, pushing forward the divisor of `f` on the chart gives the divisor of
  the reduction of `f`. -/
  mapDomain_placeMap : ∀ f : integers, residue f ≠ 0 → ∀ D : Divisor L F,
    (∀ P ∈ dom, D P = P.ord (f : F)) → (∀ P, P ∉ dom → D P = 0) →
      ∀ Q, Q ∉ nodes → Finsupp.mapDomain placeMap D Q = Q.ord (residue f)

/-- An open annulus of rational places of `F`, with coordinate `param` and modulus in the
maximal ideal of `A`. -/
structure Annulus where
  /-- The places of the annulus. -/
  dom : Set (Place L F)
  /-- The annulus coordinate. -/
  param : F
  /-- The modulus of the annulus. -/
  modulus : A
  /-- The modulus lies in the maximal ideal of `A`. -/
  modulus_mem : modulus ∈ maximalIdeal A
  /-- At every place of the annulus the coordinate takes a nonzero value in the maximal ideal of
  `A` dividing the modulus by an element of the maximal ideal. -/
  mem_dom : ∀ P ∈ dom, P.IsRational ∧ param ∈ P.toValuationSubring ∧
    (∃ h : P.evalAt param ∈ A, (⟨P.evalAt param, h⟩ : A) ∈ maximalIdeal A) ∧
    P.evalAt param ≠ 0 ∧ ∃ m ∈ maximalIdeal A, (modulus : L) = P.evalAt param * m
  /-- Every admissible value of the coordinate is taken at exactly one place of the annulus. -/
  existsUnique_evalAt_eq : ∀ c : A, c ∈ maximalIdeal A → (c : L) ≠ 0 →
    (∃ m ∈ maximalIdeal A, (modulus : L) = c * m) →
      ∃! P : Place L F, P ∈ dom ∧ P.evalAt param = c
  /-- The coordinate is a local parameter at each place of the annulus. -/
  ord_param_sub : ∀ P ∈ dom, P.ord (param - algebraMap L F (P.evalAt param)) = 1
  /-- A function without zeros or poles on the annulus is a constant times a power of the
  coordinate times a unit, uniformly on the annulus. -/
  unit_principle : ∀ f : F, f ≠ 0 → (∀ P ∈ dom, P.ord f = 0) →
    ∃ (m : ℤ) (c : L), c ≠ 0 ∧
      ∀ P ∈ dom, ∃ h : P.evalAt f * c⁻¹ * (P.evalAt param) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A)

namespace Annulus

variable {A F Fbar}

/-- The annulus `An` is attached to the component chart `C` at the node `x`: the coordinate is
integral for `C` and reduces to a uniformizer at `x`, and every unit on the annulus with nonzero
reduction has absolute value `|z|^(ord_x)` there, up to a unit of `A`. -/
def IsAttached (An : Annulus A F) (C : ComponentChart A F Fbar)
    (x : Place (IsLocalRing.ResidueField A) Fbar) : Prop :=
  x ∈ C.nodes ∧ ∃ hz : An.param ∈ C.integers, x.ord (C.residue ⟨An.param, hz⟩) = 1 ∧
    ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
      ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x.ord (C.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A)

end Annulus

end AlgebraicCurve
