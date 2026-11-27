/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihGapOneBoundary
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihGapOneIndex

/-!
# Alexander--Whitney/shuffle part of the gap-one Shih boundary

The front faces of the gap-one family are exactly the positive-front-degree
summands in the degreewise Alexander--Whitney/shuffle composite.  This file
isolates the omitted front-degree-zero term.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial SimplexCategory
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

/-- The left simplex endomorphism in one degreewise `AW ≫ shuffle` summand. -/
def awShuffleLeftHom (n : ℕ) (p : Fin (n + 1))
    (s : Shuffle p (n - (p : ℕ))) : ⦋n⦌ ⟶ ⦋n⦌ :=
  eqToHom (by
      have hp := p.isLt
      congr 1
      omega) ≫
    s.leftHom ≫
      AlexanderWhitney.frontInclusion (p : ℕ) (n - (p : ℕ)) n (by
        have hp := p.isLt
        omega)

/-- The right simplex endomorphism in one degreewise `AW ≫ shuffle` summand. -/
def awShuffleRightHom (n : ℕ) (p : Fin (n + 1))
    (s : Shuffle p (n - (p : ℕ))) : ⦋n⦌ ⟶ ⦋n⦌ :=
  eqToHom (by
      have hp := p.isLt
      congr 1
      omega) ≫
    s.rightHom ≫
      AlexanderWhitney.backInclusion (p : ℕ) (n - (p : ℕ)) n (by
        have hp := p.isLt
        omega)

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- One degreewise `AW ≫ shuffle` summand, written without choosing a
homological-complex tensor decomposition. -/
def awShuffleDiagonalSummand (X Y : SimplicialObject C) (n : ℕ)
    (p : Fin (n + 1)) (s : Shuffle p (n - (p : ℕ))) :
    X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) ⟶
      X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) :=
  shuffleSignZ s •
    (X.map (awShuffleLeftHom n p s).op ⊗ₘ Y.map (awShuffleRightHom n p s).op)

theorem gapOneBaseSummand_eq_awShuffleDiagonalSummand
    (X Y : SimplicialObject C) (n : ℕ) (x : ShihIndex.GapOneShuffleIndex n) :
    gapOneBaseSummand X Y ((ShihIndex.gapOneEquiv n).symm x).1
        ((ShihIndex.gapOneEquiv n).symm x).2 =
      awShuffleDiagonalSummand X Y n x.1.succ x.2 := by
  rcases x with ⟨p, s⟩
  dsimp only [ShihIndex.gapOneEquiv, ShihIndex.ofGapOneShuffleIndex,
    Equiv.symm_apply_apply]
  unfold gapOneBaseSummand ShihIndex.gapOneBaseLeftHom
    ShihIndex.gapOneBaseRightHom awShuffleDiagonalSummand awShuffleLeftHom
    awShuffleRightHom
  rfl

/-- The full degreewise `AW ≫ shuffle` sum at the diagonal simplicial-object
level. -/
def awShuffleDiagonalComponent (X Y : SimplicialObject C) (n : ℕ) :
    X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) ⟶
      X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) :=
  ∑ p : Fin (n + 1),
    ∑ s : Shuffle p (n - (p : ℕ)), awShuffleDiagonalSummand X Y n p s

/-- The front-degree-zero part omitted by the gap-one Shih family. -/
def awShuffleZeroComponent (X Y : SimplicialObject C) (n : ℕ) :
    X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) ⟶
      X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) :=
  ∑ s : Shuffle 0 n, awShuffleDiagonalSummand X Y n 0 s

theorem sum_gapOneBaseSummand (X Y : SimplicialObject C) (n : ℕ) :
    ∑ i : {i : ShihIndex n // i.gap = 1}, gapOneBaseSummand X Y i.1 i.2 =
      ∑ p : Fin n, ∑ s : Shuffle (p.val + 1) (n - (p.val + 1)),
        awShuffleDiagonalSummand X Y n p.succ s := by
  calc
    _ = ∑ x : ShihIndex.GapOneShuffleIndex n,
          gapOneBaseSummand X Y ((ShihIndex.gapOneEquiv n).symm x).1
            ((ShihIndex.gapOneEquiv n).symm x).2 := by
      simpa using (ShihIndex.gapOneEquiv n).sum_comp
        (fun x => gapOneBaseSummand X Y
          ((ShihIndex.gapOneEquiv n).symm x).1
          ((ShihIndex.gapOneEquiv n).symm x).2)
    _ = _ := by
      refine (Fintype.sum_sigma (fun x : ShihIndex.GapOneShuffleIndex n =>
        gapOneBaseSummand X Y ((ShihIndex.gapOneEquiv n).symm x).1
          ((ShihIndex.gapOneEquiv n).symm x).2)).trans ?_
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ =>
        gapOneBaseSummand_eq_awShuffleDiagonalSummand X Y n ⟨p, s⟩

/-- The gap-one base sum is the full `AW ≫ shuffle` sum minus its
front-degree-zero term. -/
theorem sum_gapOneBaseSummand_eq_awShuffle_sub_zero
    (X Y : SimplicialObject C) (n : ℕ) :
    ∑ i : {i : ShihIndex n // i.gap = 1}, gapOneBaseSummand X Y i.1 i.2 =
      awShuffleDiagonalComponent X Y n - awShuffleZeroComponent X Y n := by
  rw [eq_sub_iff_add_eq, add_comm]
  unfold awShuffleDiagonalComponent awShuffleZeroComponent
  rw [Fin.sum_univ_succ, sum_gapOneBaseSummand]
  rfl

end AlgebraicTopology.EilenbergZilber
