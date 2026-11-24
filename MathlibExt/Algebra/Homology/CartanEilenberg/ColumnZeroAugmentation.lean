/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.Bicomplex
public import MathlibExt.Algebra.Homology.VerticalHomologyComplex

/-!
# The column-zero augmentation of a Cartan--Eilenberg resolution

The augmentations of the stored term resolutions assemble in resolution
degree zero into a map to the original chain complex.  Taking homology in a
fixed original degree then gives the degree-zero component of a strict map
from the vertical-homology complex to the corresponding single complex.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

namespace CartanEilenbergResolution

set_option backward.isDefEq.respectTransparency false in
/-- The term-resolution augmentations in resolution degree zero, assembled
as a map of chain complexes in the original degree. -/
noncomputable def termColumnZeroAugmentation :
    P.bicomplex.X 0 ⟶ L :=
  ChainComplex.ofHom
    (fun j => (P.termResolution j).π.f 0)
    (fun j => by
      rw [P.bicomplex_d₂ 0 j]
      change (P.termResolution (j + 1)).π.f 0 ≫ L.d (j + 1) j =
        (P.termDifferential j).f 0 ≫ (P.termResolution j).π.f 0
      have h := HomologicalComplex.congr_hom
        (P.termDifferential_comp_π j) 0
      simpa only [HomologicalComplex.comp_f,
        ChainComplex.single₀_map_f_zero] using h.symm)

/-- The column-zero augmentation is the stored term-resolution augmentation
in every original degree. -/
@[simp]
theorem termColumnZeroAugmentation_f (j : ℕ) :
    P.termColumnZeroAugmentation.f j =
      (P.termResolution j).π.f 0 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The first resolution differential is killed by the column-zero
augmentation. -/
@[reassoc]
theorem bicomplex_d_one_zero_comp_termColumnZeroAugmentation :
    P.bicomplex.d 1 0 ≫ P.termColumnZeroAugmentation = 0 := by
  apply HomologicalComplex.hom_ext
  intro j
  change (P.bicomplex.d 1 0).f j ≫
      P.termColumnZeroAugmentation.f j = 0
  rw [P.bicomplex_d₁ 0 j, P.termColumnZeroAugmentation_f]
  exact (P.termResolution j).complex_d_comp_π_f_zero

/-- The map on homology induced by the column-zero augmentation in original
degree `q`. -/
noncomputable def termColumnZeroHomologyAugmentation (q : ℕ) :
    (P.bicomplex.verticalHomologyComplex q).X 0 ⟶ L.homology q :=
  HomologicalComplex.homologyMap P.termColumnZeroAugmentation q

/-- The homology augmentation is the homology map of the assembled column
augmentation. -/
theorem termColumnZeroHomologyAugmentation_eq_homologyMap (q : ℕ) :
    P.termColumnZeroHomologyAugmentation q =
      HomologicalComplex.homologyMap P.termColumnZeroAugmentation q :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The first differential of the vertical-homology complex is killed by its
degree-zero augmentation. -/
@[reassoc]
theorem verticalHomologyComplex_d_one_zero_comp_termColumnZeroHomologyAugmentation
    (q : ℕ) :
    (P.bicomplex.verticalHomologyComplex q).d 1 0 ≫
        P.termColumnZeroHomologyAugmentation q = 0 := by
  rw [P.bicomplex.verticalHomologyComplex_d 1 0 q]
  change HomologicalComplex.homologyMap (P.bicomplex.d 1 0) q ≫
      HomologicalComplex.homologyMap P.termColumnZeroAugmentation q = 0
  rw [← HomologicalComplex.homologyMap_comp,
    P.bicomplex_d_one_zero_comp_termColumnZeroAugmentation,
    HomologicalComplex.homologyMap_zero]

/-- The strict augmentation of the vertical-homology complex in original
degree `q`. -/
noncomputable def rowHomologyAugmentation (q : ℕ) :
    P.bicomplex.verticalHomologyComplex q ⟶
      (ChainComplex.single₀ C).obj (L.homology q) :=
  (ChainComplex.toSingle₀Equiv
    (P.bicomplex.verticalHomologyComplex q) (L.homology q)).symm
      ⟨P.termColumnZeroHomologyAugmentation q,
        P.verticalHomologyComplex_d_one_zero_comp_termColumnZeroHomologyAugmentation q⟩

/-- The degree-zero component of the row-homology augmentation is the
homology map induced by the full term-column augmentation. -/
@[simp]
theorem rowHomologyAugmentation_f_zero (q : ℕ) :
    (P.rowHomologyAugmentation q).f 0 =
      P.termColumnZeroHomologyAugmentation q :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- Every positive-degree component of the row-homology augmentation is
zero. -/
@[simp]
theorem rowHomologyAugmentation_f_succ (q n : ℕ) :
    (P.rowHomologyAugmentation q).f (n + 1) = 0 := by
  apply (HomologicalComplex.isZero_single_obj_X
    (ComplexShape.down ℕ) 0 (L.homology q) (n + 1)
      (Nat.succ_ne_zero n)).eq_of_tgt

end CartanEilenbergResolution

end HomologicalComplex

end
