/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.ShuffleBridges

/-!
# Shuffle Bridges Test
-/

set_option pp.universes true

open CategoryTheory Limits MonoidalCategory

namespace SSet

open MonoidalClosed

/-! # Smoke / regression tests for `ShuffleBridges` (the supporting result)

Checks:
(a) Shuffle initials, special edges, and horn verticals have
    the stated types, components, and memberships.
(b) The cell inputs `ShuffleHornZero/TwoCellExtension` are
    substantive `Prop`s (not `trivial`-provable), and the
    `Δ[2]` cell bridges turn them into horn-prism extension
    along `∂Δ[n].ι`.
(c) The `Δ[1]` bridges along `∂Δ[n].ι` and along single-cell
    attachments hold unconditionally; the `n = 0` cases need
    no quasicategory hypothesis.
(d) Verticals of an equivalence-edge prism are equivalences,
    and prism extension is stable under composition and
    cobase change at the stated types.
-/

universe u

open scoped Simplicial

-- (a) initials, special edges, horn verticals.

example (n : ℕ) :
    (shuffleInit0.{u} n : (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) =
      Subcomplex.unionProd ∂Δ[n] Λ[2, 0] := rfl

example (n : ℕ) :
    (shuffleInit2.{u} n : (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) =
      Subcomplex.unionProd ∂Δ[n] Λ[2, 2] := rfl

example (n : ℕ) :
    (shuffleVert0.{u} n).2 = shuffleEdge01.{u} :=
  shuffleVert0_snd.{u} n

example (n : ℕ) :
    (shuffleVert2.{u} n).2 = shuffleEdge12.{u} :=
  shuffleVert2_snd.{u} n

example (n : ℕ) :
    shuffleVert0.{u} n ∈ (shuffleInit0.{u} n).obj
      (Opposite.op ⦋1⦌) :=
  shuffleVert0_mem_shuffleInit0.{u} n

example (n : ℕ) :
    shuffleVert2.{u} n ∈ (shuffleInit2.{u} n).obj
      (Opposite.op ⦋1⦌) :=
  shuffleVert2_mem_shuffleInit2.{u} n

example : shuffleEdge01.{u} ∈ Λ[2, (0 : Fin 3)].obj
    (Opposite.op ⦋1⦌) :=
  shuffleEdge01_mem_hornZero.{u}

example : shuffleEdge12.{u} ∈ Λ[2, (2 : Fin 3)].obj
    (Opposite.op ⦋1⦌) :=
  shuffleEdge12_mem_hornTwo.{u}

example {B : SSet.{u}} (x : B _⦋0⦌) :
    (hornVertZeroSimplex.{u} x).1 = B.σ 0 x :=
  hornVertZeroSimplex_fst.{u} x

example {B : SSet.{u}} (x : B _⦋0⦌) :
    (hornVertTwoSimplex.{u} x).2.val = shuffleEdge12.{u} :=
  hornVertTwoSimplex_snd_val.{u} x

example (n : ℕ) :
    prismVertZero.{u} n =
      verticalOneSimplex.{u} (stdSimplex.obj₀Equiv.symm 0) :=
  prismVertZero_eq_verticalOneSimplex.{u} n

example (n : ℕ) :
    prismVertLast.{u} n =
      verticalOneSimplex.{u}
        (stdSimplex.obj₀Equiv.symm (Fin.last n)) :=
  prismVertLast_eq_verticalOneSimplex.{u} n

-- (b) the cell inputs are substantive, and the `Δ[2]` bridges.

example (n : ℕ) (C : SSet.{u}) [C.Quasicategory] : Prop :=
  ShuffleHornZeroCellExtension.{u} n C

example (n : ℕ) (C : SSet.{u}) [C.Quasicategory] : Prop :=
  ShuffleHornTwoCellExtension.{u} n C

-- Note: the cell extensions are definitions of the required
-- shuffle-filling inputs, not theorems (the additional comparison obligation); they
-- must therefore not be `trivial`-provable.
example (n : ℕ) (C : SSet.{u}) [C.Quasicategory] :
    ShuffleHornZeroCellExtension.{u} n C ∨ True := by
  fail_if_success (exact Or.inl trivial)
  exact Or.inr trivial

example {n : ℕ} {C : SSet.{u}} [C.Quasicategory]
    (hcell : ShuffleHornZeroCellExtension.{u} n C) :
    PrismTwoHornZeroExtension.{u} ∂Δ[n].ι C :=
  prismTwoHornZeroExtension_boundary_of_shuffleCell.{u} hcell

example {n : ℕ} {C : SSet.{u}} [C.Quasicategory]
    (hcell : ShuffleHornTwoCellExtension.{u} n C) :
    PrismTwoHornTwoExtension.{u} ∂Δ[n].ι C :=
  prismTwoHornTwoExtension_boundary_of_shuffleCell.{u} hcell

-- (c) unconditional `Δ[1]` bridges and cell attachments.

example {n : ℕ} {C : SSet.{u}} [C.Quasicategory] :
    PrismSrcExtension.{u} ∂Δ[n].ι C :=
  prismSrcExtension_boundary.{u}

example {n : ℕ} {C : SSet.{u}} [C.Quasicategory] :
    PrismTgtExtension.{u} ∂Δ[n].ι C :=
  prismTgtExtension_boundary.{u}

-- The `n = 0` cases need no quasicategory hypothesis.
example (C : SSet.{u}) : PrismSrcExtension.{u} ∂Δ[0].ι C :=
  prismSrcExtension_boundary_zero.{u} C

example (C : SSet.{u}) : PrismTgtExtension.{u} ∂Δ[0].ι C :=
  prismTgtExtension_boundary_zero.{u} C

example {n : ℕ} {C X Y : SSet.{u}} [C.Quasicategory]
    {f : (∂Δ[n] : SSet.{u}) ⟶ X} {f' : Δ[n] ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout ∂Δ[n].ι f f' j) :
    PrismSrcExtension.{u} j C :=
  prismSrcExtension_of_isPushout_boundary.{u} sq

example {n : ℕ} {C X Y : SSet.{u}} [C.Quasicategory]
    {f : (∂Δ[n] : SSet.{u}) ⟶ X} {f' : Δ[n] ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout ∂Δ[n].ι f f' j) :
    PrismTgtExtension.{u} j C :=
  prismTgtExtension_of_isPushout_boundary.{u} sq

-- (d) vertical evaluations and closure operations.

example {A C : SSet.{u}} {a₀ a₁ : ((ihom A).obj C) _⦋0⦌}
    (e : Edge a₀ a₁) (x : A _⦋0⦌) :
    (ihomPrismOfSimplex.{u} e.edge).app _
        (verticalOneSimplex.{u} x) =
      ((e.map ((pre (yonedaEquiv.symm x)).app C)).map
        (evalDeltaZeroIso.{u} C).hom).edge :=
  ihomPrismOfSimplex_app_verticalOneSimplex.{u} e x

example {A C : SSet.{u}} {a₀ a₁ : ((ihom A).obj C) _⦋0⦌}
    (e : Edge a₀ a₁) (he : e.IsEquivalence) :
    PrismOneVerticalsEquivalences.{u}
      (ihomPrismOfSimplex.{u} e.edge) :=
  prismOneVerticalsEquivalences_ihomPrismOfSimplex_of_isEquivalence.{u}
    e he

example {F₀ : (Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶ (Δ[2] : SSet.{u})} :
    ((evalDeltaZeroIso.{u} (Δ[2] : SSet.{u})).hom).app
        (Opposite.op ⦋1⦌)
        (ihomSimplexOfPrism.{u} F₀) =
      F₀.app (Opposite.op ⦋1⦌)
        (verticalOneSimplex.{u} (stdSimplex.obj₀Equiv.symm 0)) :=
  evalDeltaZeroIso_hom_app_ihomSimplexOfPrism_one.{u} F₀

example {A B D C : SSet.{u}} {i : A ⟶ B} {j : B ⟶ D}
    (hi : PrismSrcExtension.{u} i C)
    (hj : PrismSrcExtension.{u} j C) :
    PrismSrcExtension.{u} (i ≫ j) C :=
  PrismSrcExtension.comp.{u} hi hj

example {A B X Y C : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X}
    {f' : B ⟶ Y} {j : X ⟶ Y} (sq : IsPushout i f f' j)
    (h : PrismSrcExtension.{u} i C) :
    PrismSrcExtension.{u} j C :=
  PrismSrcExtension.of_isPushout.{u} sq h

example {A B X Y C : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X}
    {f' : B ⟶ Y} {j : X ⟶ Y} (sq : IsPushout i f f' j)
    (h : PrismTgtExtension.{u} i C) :
    PrismTgtExtension.{u} j C :=
  PrismTgtExtension.of_isPushout.{u} sq h

example {A B X Y : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X}
    {f' : B ⟶ Y} {j : X ⟶ Y} (sq : IsPushout i f f' j)
    (y : Y _⦋0⦌) :
    (∃ b : B _⦋0⦌, f'.app _ b = y) ∨
      (∃ x : X _⦋0⦌, j.app _ x = y) :=
  exists_app_eq_zero_of_isPushout.{u} sq y

end SSet
