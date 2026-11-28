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
# Degreewise splittings of Cartan–Eilenberg horseshoes

Let P be Cartan–Eilenberg resolution data in an abelian category. At resolution degree a and
original degree j, the chosen coordinates give PBⱼ₊₁,ₐ → PCⱼ,ₐ → PHⱼ,ₐ as the standard split
biproduct sequence, and PCⱼ,ₐ → PTⱼ,ₐ → PBⱼ,ₐ as the second standard split biproduct sequence.

Transporting the biproduct retractions and sections gives explicit splittings of both evaluated
horseshoe rows.
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

/-- Let C be abelian, L a nonnegative complex and P a Cartan–Eilenberg resolution, with resolutions
PBⱼ of outgoing boundaries, PCⱼ of cycles, PTⱼ of terms and PHⱼ of homology. Fix resolution
degree a and original degree j. The evaluated cycle horseshoe is the short complex PBⱼ₊₁,ₐ →
PCⱼ,ₐ → PHⱼ,ₐ. -/
noncomputable abbrev cyclesComponentShortComplex (a j : ℕ) :
    ShortComplex C :=
  (P.cyclesShortComplex j).map
    (HomologicalComplex.eval C (ComplexShape.down ℕ) a)

/-- Let C be abelian, L a nonnegative complex and P a Cartan–Eilenberg resolution, with resolutions
PBⱼ of outgoing boundaries, PCⱼ of cycles, PTⱼ of terms and PHⱼ of homology. Fix resolution
degree a and original degree j. The cycle row has the standard biproduct model PBⱼ₊₁,ₐ → PBⱼ₊₁,ₐ
⊕ PHⱼ,ₐ → PHⱼ,ₐ, with first inclusion and second projection. -/
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
/-- Let C be abelian, L a nonnegative complex and P a Cartan–Eilenberg resolution, with resolutions
PBⱼ of outgoing boundaries, PCⱼ of cycles, PTⱼ of terms and PHⱼ of homology. Fix resolution
degree a and original degree j. The stored cycle coordinates give an isomorphism from PBⱼ₊₁,ₐ →
PCⱼ,ₐ → PHⱼ,ₐ to its standard biproduct short complex, preserving the endpoint maps. -/
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

/-- Let C be abelian, L a nonnegative complex and P a Cartan–Eilenberg resolution, with resolutions
PBⱼ of outgoing boundaries, PCⱼ of cycles, PTⱼ of terms and PHⱼ of homology. Fix resolution
degree a and original degree j. The retraction and section from the standard biproduct
coordinates give a splitting of PBⱼ₊₁,ₐ → PCⱼ,ₐ → PHⱼ,ₐ. -/
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

/-- Let C be abelian, L a nonnegative complex and P a Cartan–Eilenberg resolution, with resolutions
PBⱼ of outgoing boundaries, PCⱼ of cycles, PTⱼ of terms and PHⱼ of homology. Fix resolution
degree a and original degree j. The evaluated term horseshoe is the short complex PCⱼ,ₐ → PTⱼ,ₐ
→ PBⱼ,ₐ. -/
noncomputable abbrev termComponentShortComplex (a j : ℕ) :
    ShortComplex C :=
  (P.termShortComplex j).map
    (HomologicalComplex.eval C (ComplexShape.down ℕ) a)

/-- Let C be abelian, L a nonnegative complex and P a Cartan–Eilenberg resolution, with resolutions
PBⱼ of outgoing boundaries, PCⱼ of cycles, PTⱼ of terms and PHⱼ of homology. Fix resolution
degree a and original degree j. The term row has the standard biproduct model PCⱼ,ₐ → PCⱼ,ₐ ⊕
PBⱼ,ₐ → PBⱼ,ₐ, with the first inclusion and second projection. -/
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
/-- Let C be abelian, L a nonnegative complex and P a Cartan–Eilenberg resolution, with resolutions
PBⱼ of outgoing boundaries, PCⱼ of cycles, PTⱼ of terms and PHⱼ of homology. Fix resolution
degree a and original degree j. The stored term coordinates give an isomorphism from PCⱼ,ₐ →
PTⱼ,ₐ → PBⱼ,ₐ to its standard biproduct short complex, preserving both endpoint arrows. -/
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

/-- Let C be abelian, L a nonnegative complex and P a Cartan–Eilenberg resolution, with resolutions
PBⱼ of outgoing boundaries, PCⱼ of cycles, PTⱼ of terms and PHⱼ of homology. Fix resolution
degree a and original degree j. The standard biproduct retraction and section, transported
through the term coordinates, split PCⱼ,ₐ → PTⱼ,ₐ → PBⱼ,ₐ. -/
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
