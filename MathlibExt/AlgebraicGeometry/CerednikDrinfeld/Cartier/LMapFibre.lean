/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source file at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_CerednikDrinfeld_CartierLMapFibre.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.CriticalIndexChart
public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.NModule

/-!
# λ-maps and their fibres

For a formal `O_D`-module `X` over a ring of characteristic `p`, `FormalODModule.piOp` is the
action of `ϖ` on the Cartier module, `FormalODModule.NMod` and `FormalODModule.lambdaN` are the
module `N` and its map `λ` for the pair `(V, Π)`, and `FormalODModule.NPiece` its graded pieces.
`FormalODModule.IsLMap` collects the conditions on a lift `L` of Frobenius through `λ`:
compatibility with Verschiebung and the grading, and prescribed values in critical degrees.
For such `L`, `IsLMap.phi`, `IsLMap.eta` and `IsLMap.u` are the induced operator, its fixed
points and their image in the Lie algebra.

These need no complementary graded pieces. When the pieces `0` and `1` are complementary,
`GradedCartierModuleData.NMod` of `toGradedCartierModuleData` is, as an additive group, the
quotient of `M × M` by the same pairs `(V m, -Π m)`: its `ϖ` acts as `piOp`, and its `V` is
`verschiebungInt`, which is `verschiebung` in characteristic `p`
(`verschiebungInt_eq_verschiebung`).

## References

* J.-F. Boutot and H. Carayol, *Uniformisation p-adique des courbes de Shimura : les théorèmes
  de Čerednik et de Drinfeld*, in *Courbes modulaires et courbes de Shimura*, Astérisque
  196–197 (1991), 45–158, for special formal `O_D`-modules and their Cartier modules.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

abbrev piOp (X : FormalODModule p B) : CartierModule p X.F →+ CartierModule p X.F :=
  CartierModule.map X.varpiEnd

theorem piOp_apply (X : FormalODModule p B) (f : CartierModule p X.F) :
    X.piOp f = CartierModule.endAct X.varpiEnd f := rfl

theorem piOp_comp_verschiebung [CharP B p] (X : FormalODModule p B) :
    X.piOp.comp CartierModule.verschiebung = CartierModule.verschiebung.comp X.piOp :=
  AddMonoidHom.ext fun f => CartierModule.map_verschiebung X.varpiEnd f

abbrev NMod [CharP B p] (X : FormalODModule p B) : Type u :=
  CartierN.NMod (CartierModule.verschiebung (p := p) (Φ := X.F)) X.piOp

abbrev lambdaN [CharP B p] (X : FormalODModule p B) : X.NMod →+ CartierModule p X.F :=
  CartierN.lambda CartierModule.verschiebung X.piOp X.piOp_comp_verschiebung

abbrev NPiece [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) : AddSubgroup X.NMod :=
  CartierN.piece CartierModule.verschiebung X.piOp (X.gradedPiece j n) (X.gradedPiece j n)

theorem critChart_isCritical_iff [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    CritChart.IsCritical X j n ↔
      ∀ f ∈ X.gradedPiece j n, ∃ g : CartierModule p X.F, X.piOp f = CartierModule.verschiebung g :=
  forall₂_congr fun _ _ => exists_congr fun _ => eq_comm

theorem mem_critChart_invariants_iff [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (m : CartierModule p X.F) :
    m ∈ CritChart.invariants X j n ↔ m ∈ X.gradedPiece j n ∧ X.piOp m =
        CartierModule.verschiebung m :=
  Iff.rfl

def IsPiBijective [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) : Prop :=
  (∀ f ∈ X.gradedPiece j n, (∃ g : CartierModule p X.F, CartierModule.verschiebung g = X.piOp f) →
      ∃ g : CartierModule p X.F, CartierModule.verschiebung g = f) ∧
    ∀ h ∈ X.gradedPiece j (n + 1), ∃ f ∈ X.gradedPiece j n, ∃ g : CartierModule p X.F,
      h = X.piOp f + CartierModule.verschiebung g

/-- **`L`-map.** Let `X` be a formal `O_D`-module over a commutative ring `B` of characteristic
`p`, `j : Zp2 p →+* B` a ring homomorphism, `M` the Cartier module of `X`, `Π` the action of `ϖ`
on `M`, `N` the quotient of `M × M` by the pairs `(V m, -Π m)`, and `λ : N → M` the map
`(m, m') ↦ Π m + V m'`. An additive map `L : M → N` is an `L`-map when `λ ∘ L = F`, `L (V m)`
is the class of `(Π m, 0)`, `L` maps the graded piece `n` of `M` into the classes of pairs of
elements of the graded piece `n`, and, for every critical index `n`, `L f` is the class of
`(g, 0)` whenever `f` lies in the graded piece `n` and `V g = Π f`. -/
structure IsLMap [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B)
    (L : CartierModule p X.F →+ X.NMod) : Prop where

  lambdaN_comp : X.lambdaN.comp L = CartierModule.frobenius

  comp_verschiebung :
    L.comp CartierModule.verschiebung = (CartierN.inl CartierModule.verschiebung X.piOp).comp X.piOp

  mem_nPiece : ∀ (n : ℕ), ∀ f ∈ X.gradedPiece j n, L f ∈ X.NPiece j n

  eq_inl_of_isCritical : ∀ (n : ℕ), CritChart.IsCritical X j n → ∀ f ∈ X.gradedPiece j n,
    ∀ g : CartierModule p X.F, CartierModule.verschiebung g = X.piOp f →
      L f = CartierN.inl CartierModule.verschiebung X.piOp g

namespace IsLMap

variable [CharP B p] {X : FormalODModule p B} {j : Zp2 p →+* B} {L : CartierModule p X.F →+ X.NMod}

abbrev phi (h : X.IsLMap j L) : X.NMod →+ X.NMod :=
  CartierN.phi CartierModule.verschiebung X.piOp L h.comp_verschiebung

abbrev eta (h : X.IsLMap j L) : AddSubgroup X.NMod :=
  CartierN.eta CartierModule.verschiebung X.piOp L h.comp_verschiebung

abbrev u (h : X.IsLMap j L) :
    h.eta →+ CartierModule p X.F ⧸ (CartierModule.verschiebung (p := p) (Φ := X.F)).range :=
  CartierN.u CartierModule.verschiebung X.piOp L h.comp_verschiebung

end IsLMap

end FormalODModule

end CerednikDrinfeld

end
