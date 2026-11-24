/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module


public import MathlibExt.Algebra.Homology.CartanEilenberg.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Degreewise splittings of Cartan--Eilenberg rows

The coordinate specifications stored in a Cartan--Eilenberg resolution identify each evaluated
horseshoe row with the canonical biproduct short complex.  This file transports its standard
splitting back to the row.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.CartanEilenbergResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

/-- The boundary--cycle--homology row evaluated in one resolution degree. -/
noncomputable abbrev cyclesComponentShortComplex (a j : ℕ) :
    ShortComplex C :=
  (P.cyclesShortComplex j).map
    (HomologicalComplex.eval C (ComplexShape.down ℕ) a)

/-- The canonical biproduct model of the evaluated boundary--cycle--homology
row. -/
noncomputable abbrev cyclesComponentBiprodShortComplex (a j : ℕ) :
    ShortComplex C :=
  ShortComplex.mk
    (biprod.inl :
      (P.boundaryResolution (j + 1)).complex.X a ⟶
        (P.boundaryResolution (j + 1)).complex.X a ⊞
          (P.homologyResolution j).complex.X a)
    (biprod.snd :
      (P.boundaryResolution (j + 1)).complex.X a ⊞
          (P.homologyResolution j).complex.X a ⟶
        (P.homologyResolution j).complex.X a)
    (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The evaluated boundary--cycle--homology row in the stored horseshoe
coordinates. -/
noncomputable def cyclesComponentShortComplexIso (a j : ℕ) :
    P.cyclesComponentShortComplex a j ≅
      P.cyclesComponentBiprodShortComplex a j :=
  ShortComplex.isoMk (Iso.refl _)
    ((P.cyclesSpec j).middleXIso a) (Iso.refl _)
    (by
      simpa only [cyclesComponentShortComplex,
        cyclesComponentBiprodShortComplex,
        CartanEilenbergResolution.cyclesShortComplex,
        ShortComplex.map_f, HomologicalComplex.eval_map,
        Iso.refl_hom, Category.id_comp] using
          ((P.cyclesSpec j).i_f a).symm)
    (by
      have hp : ((P.cyclesSpec j).middleXIso a).hom ≫ biprod.snd =
          (P.cyclesHorseshoe j).p.f a := by
        rw [← (P.cyclesSpec j).p_f a]
        simp
      simpa only [cyclesComponentShortComplex,
        cyclesComponentBiprodShortComplex,
        CartanEilenbergResolution.cyclesShortComplex,
        ShortComplex.map_g, HomologicalComplex.eval_map,
        Iso.refl_hom, Category.comp_id] using hp)

/-- The explicit splitting of the evaluated boundary--cycle--homology row. -/
noncomputable def cyclesComponentSplitting (a j : ℕ) :
    (P.cyclesComponentShortComplex a j).Splitting :=
  ShortComplex.Splitting.ofIso
    (ShortComplex.Splitting.ofHasBinaryBiproduct
      ((P.boundaryResolution (j + 1)).complex.X a)
      ((P.homologyResolution j).complex.X a))
    (P.cyclesComponentShortComplexIso a j).symm

@[simp]
theorem cyclesComponentSplitting_r (a j : ℕ) :
    (P.cyclesComponentSplitting a j).r =
      ((P.cyclesSpec j).middleXIso a).hom ≫ biprod.fst := by
  dsimp [cyclesComponentSplitting, ShortComplex.Splitting.ofIso,
    ShortComplex.Splitting.ofHasBinaryBiproduct,
    cyclesComponentShortComplexIso]
  simp

@[simp]
theorem cyclesComponentSplitting_s (a j : ℕ) :
    (P.cyclesComponentSplitting a j).s =
      biprod.inr ≫ ((P.cyclesSpec j).middleXIso a).inv := by
  dsimp [cyclesComponentSplitting, ShortComplex.Splitting.ofIso,
    ShortComplex.Splitting.ofHasBinaryBiproduct,
    cyclesComponentShortComplexIso]
  simp

/-- The cycle--term--boundary row evaluated in one resolution degree. -/
noncomputable abbrev termComponentShortComplex (a j : ℕ) :
    ShortComplex C :=
  (P.termShortComplex j).map
    (HomologicalComplex.eval C (ComplexShape.down ℕ) a)

/-- The canonical biproduct model of the evaluated cycle--term--boundary
row. -/
noncomputable abbrev termComponentBiprodShortComplex (a j : ℕ) :
    ShortComplex C :=
  ShortComplex.mk
    (biprod.inl :
      (P.cyclesResolution j).complex.X a ⟶
        (P.cyclesResolution j).complex.X a ⊞
          (P.boundaryResolution j).complex.X a)
    (biprod.snd :
      (P.cyclesResolution j).complex.X a ⊞
          (P.boundaryResolution j).complex.X a ⟶
        (P.boundaryResolution j).complex.X a)
    (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The evaluated cycle--term--boundary row in the stored horseshoe
coordinates. -/
noncomputable def termComponentShortComplexIso (a j : ℕ) :
    P.termComponentShortComplex a j ≅
      P.termComponentBiprodShortComplex a j :=
  ShortComplex.isoMk (Iso.refl _)
    ((P.termSpec j).middleXIso a) (Iso.refl _)
    (by
      simpa only [termComponentShortComplex,
        termComponentBiprodShortComplex,
        CartanEilenbergResolution.termShortComplex,
        ShortComplex.map_f, HomologicalComplex.eval_map,
        Iso.refl_hom, Category.id_comp] using
          ((P.termSpec j).i_f a).symm)
    (by
      have hp : ((P.termSpec j).middleXIso a).hom ≫ biprod.snd =
          (P.termHorseshoe j).p.f a := by
        rw [← (P.termSpec j).p_f a]
        simp
      simpa only [termComponentShortComplex,
        termComponentBiprodShortComplex,
        CartanEilenbergResolution.termShortComplex,
        ShortComplex.map_g, HomologicalComplex.eval_map,
        Iso.refl_hom, Category.comp_id] using hp)

/-- The explicit splitting of the evaluated cycle--term--boundary row. -/
noncomputable def termComponentSplitting (a j : ℕ) :
    (P.termComponentShortComplex a j).Splitting :=
  ShortComplex.Splitting.ofIso
    (ShortComplex.Splitting.ofHasBinaryBiproduct
      ((P.cyclesResolution j).complex.X a)
      ((P.boundaryResolution j).complex.X a))
    (P.termComponentShortComplexIso a j).symm

@[simp]
theorem termComponentSplitting_r (a j : ℕ) :
    (P.termComponentSplitting a j).r =
      ((P.termSpec j).middleXIso a).hom ≫ biprod.fst := by
  dsimp [termComponentSplitting, ShortComplex.Splitting.ofIso,
    ShortComplex.Splitting.ofHasBinaryBiproduct,
    termComponentShortComplexIso]
  simp

@[simp]
theorem termComponentSplitting_s (a j : ℕ) :
    (P.termComponentSplitting a j).s =
      biprod.inr ≫ ((P.termSpec j).middleXIso a).inv := by
  dsimp [termComponentSplitting, ShortComplex.Splitting.ofIso,
    ShortComplex.Splitting.ofHasBinaryBiproduct,
    termComponentShortComplexIso]
  simp

end HomologicalComplex.CartanEilenbergResolution

end
