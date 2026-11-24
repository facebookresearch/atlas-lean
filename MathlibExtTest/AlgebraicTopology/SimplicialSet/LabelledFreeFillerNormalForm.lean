/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFillerNormalForm

/-!
# Public clients of the full labelled degreewise normal form
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace SSet.LabelledFreeFillerNormalFormTest

variable {I : Type u} {K D : I → SSet.{u}} (j : ∀ s, K s ⟶ D s)
variable [∀ s, Mono (j s)]

/-- Both sides of the actual degreewise equivalence retain their data. -/
theorem roundTrips (X : SSet.{u}) (n : ℕ) (x : X _⦋n⦌)
    (s : I) (a : K s ⟶ X) (d : D s _⦋n⦌)
    (hd : d ∉ Set.range ((j s).app (op ⦋n⦌))) :
    (labelledFreeFiller.degreewiseEquiv j X n).symm
        (((labelledFreeFiller.unit j).app X).app (op ⦋n⦌) x) = Sum.inl x ∧
      (labelledFreeFiller.degreewiseEquiv j X n).symm
        ((labelledFreeFiller.cell j s a).app (op ⦋n⦌) d) =
          Sum.inr ⟨⟨s, a⟩, d, hd⟩ := by
  constructor
  · rw [← labelledFreeFiller.degreewiseEquiv_inl j X n x]
    exact Equiv.symm_apply_apply _ _
  · rw [← labelledFreeFiller.degreewiseEquiv_inr j X n ⟨s, a⟩ d hd]
    exact Equiv.symm_apply_apply _ _

/-- The normal form separates old simplices from every complementary cell simplex. -/
theorem cell_ne_old (X : SSet.{u}) (n : ℕ) (x : X _⦋n⦌)
    (s : I) (a : K s ⟶ X) (d : D s _⦋n⦌)
    (hd : d ∉ Set.range ((j s).app (op ⦋n⦌))) :
    (labelledFreeFiller.cell j s a).app (op ⦋n⦌) d ≠
      ((labelledFreeFiller.unit j).app X).app (op ⦋n⦌) x := by
  intro h
  have eq := (labelledFreeFiller.degreewiseEquiv j X n).injective
    (a₁ := Sum.inr ⟨⟨s, a⟩, d, hd⟩) (a₂ := Sum.inl x)
    (by simpa only [labelledFreeFiller.degreewiseEquiv_inl,
      labelledFreeFiller.degreewiseEquiv_inr] using h)
  cases eq

/-- Naturality applies to every map, with no monicity requirement on that map. -/
theorem mapTransport {X Y : SSet.{u}} (m : X ⟶ Y) (n : ℕ)
    (q : X _⦋n⦌ ⊕ Σ x : labelledFreeFiller.Index K X,
      {d : D x.1 _⦋n⦌ // d ∉ Set.range ((j x.1).app (op ⦋n⦌))}) :
    ((labelledFreeFiller j).map m).app (op ⦋n⦌)
        (labelledFreeFiller.degreewiseEquiv j X n q) =
      labelledFreeFiller.degreewiseEquiv j Y n
        (q.map (m.app (op ⦋n⦌)) (fun x => ⟨⟨x.1.1, x.1.2 ≫ m⟩, x.2⟩)) :=
  labelledFreeFiller.degreewiseEquiv_naturality j m n q

/-- Equal generator arrows with different labels attach distinct complementary simplices. -/
theorem duplicateCells {A B X : SSet.{u}} (i : A ⟶ B) [Mono i]
    (s t : I) (hst : s ≠ t) (a : A ⟶ X) (n : ℕ) (d : B _⦋n⦌)
    (hd : d ∉ Set.range (i.app (op ⦋n⦌))) :
    (labelledFreeFiller.cell (fun _ : I => i) s a).app (op ⦋n⦌) d ≠
      (labelledFreeFiller.cell (fun _ : I => i) t a).app (op ⦋n⦌) d := by
  intro h
  have eq := (labelledFreeFiller.degreewiseEquiv (fun _ : I => i) X n).injective
    (a₁ := Sum.inr ⟨⟨s, a⟩, d, hd⟩) (a₂ := Sum.inr ⟨⟨t, a⟩, d, hd⟩)
    (by simpa only [labelledFreeFiller.degreewiseEquiv_inr] using h)
  exact hst (congrArg (fun x => x.1.1) (Sum.inr.inj eq))

/-- Empty-domain generators still attach two distinct labelled copies. -/
theorem emptyDomainCopies {A B X : SSet.{u}} (i : A ⟶ B) (a : A ⟶ X)
    [∀ m : SimplexCategoryᵒᵖ, IsEmpty (A.obj m)] (s t : I) (hst : s ≠ t)
    (n : ℕ) (d : B _⦋n⦌) :
    (labelledFreeFiller.cell (fun _ : I => i) s a).app (op ⦋n⦌) d ≠
      (labelledFreeFiller.cell (fun _ : I => i) t a).app (op ⦋n⦌) d := by
  have : Mono i := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    rw [mono_iff_injective]
    intro x
    exact isEmptyElim x
  apply duplicateCells i s t hst a n d
  rintro ⟨x, _⟩
  exact isEmptyElim x

end SSet.LabelledFreeFillerNormalFormTest
