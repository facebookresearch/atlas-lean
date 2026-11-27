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
# Column-zero and vertical-homology augmentations

Let P be a Cartan–Eilenberg resolution of a nonnegative complex L in an abelian category. The
augmentations of its term resolutions assemble in resolution degree zero to a chain map ε :
P.bicomplex.X₀ → L. The first resolution differential is killed by ε.

For every original degree q, the map H_q(ε) augments the vertical-homology chain complex to the
complex concentrated on H_q(L) in resolution degree zero. All positive-degree components of this
augmentation are zero.
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
/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. The
degree-zero term augmentations Rⱼ,₀ → Lⱼ assemble to a chain map ε : P.bicomplex.X₀ → L in the
original degree j. -/
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

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. In each
original degree j, the component εⱼ : Rⱼ,₀ → Lⱼ of the column-zero augmentation is precisely the
degree-zero augmentation of Rⱼ. -/
@[simp]
theorem termColumnZeroAugmentation_f (j : ℕ) :
    P.termColumnZeroAugmentation.f j =
      (P.termResolution j).π.f 0 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. The first
resolution differential P.bicomplex.d(1,0) is killed by the column-zero augmentation ε:
P.bicomplex.d(1,0) ≫ ε=0. -/
@[reassoc]
theorem bicomplex_d_one_zero_comp_termColumnZeroAugmentation :
    P.bicomplex.d 1 0 ≫ P.termColumnZeroAugmentation = 0 := by
  apply HomologicalComplex.hom_ext
  intro j
  change (P.bicomplex.d 1 0).f j ≫
      P.termColumnZeroAugmentation.f j = 0
  rw [P.bicomplex_d₁ 0 j, P.termColumnZeroAugmentation_f]
  exact (P.termResolution j).complex_d_comp_π_f_zero

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. For q ∈
ℕ, the column augmentation ε induces H_q(ε) from the degree-zero object of the vertical-homology
complex to H_q(L). -/
noncomputable def termColumnZeroHomologyAugmentation (q : ℕ) :
    (P.bicomplex.verticalHomologyComplex q).X 0 ⟶ L.homology q :=
  HomologicalComplex.homologyMap P.termColumnZeroAugmentation q

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. The
homology augmentation in original degree q is exactly H_q(ε), where ε is the assembled
column-zero chain augmentation. -/
theorem termColumnZeroHomologyAugmentation_eq_homologyMap (q : ℕ) :
    P.termColumnZeroHomologyAugmentation q =
      HomologicalComplex.homologyMap P.termColumnZeroAugmentation q :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. For every
q ∈ ℕ, the first resolution differential of the vertical-homology complex is killed by H_q(ε):
d^{1,0} ≫ H_q(ε)=0. -/
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

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. For each
original degree q, H_q(ε) in resolution degree zero extends to an augmentation of the
vertical-homology chain complex to H_q(L)[0]. Its positive resolution-degree components are
zero. -/
noncomputable def rowHomologyAugmentation (q : ℕ) :
    P.bicomplex.verticalHomologyComplex q ⟶
      (ChainComplex.single₀ C).obj (L.homology q) :=
  (ChainComplex.toSingle₀Equiv
    (P.bicomplex.verticalHomologyComplex q) (L.homology q)).symm
      ⟨P.termColumnZeroHomologyAugmentation q,
        P.verticalHomologyComplex_d_one_zero_comp_termColumnZeroHomologyAugmentation q⟩

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. The
resolution-degree-zero component of the augmentation of vertical homology in degree q is H_q(ε),
the homology map of the column-zero augmentation. -/
@[simp]
theorem rowHomologyAugmentation_f_zero (q : ℕ) :
    (P.rowHomologyAugmentation q).f 0 =
      P.termColumnZeroHomologyAugmentation q :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- Let C be abelian, L a nonnegative chain complex, and P a Cartan–Eilenberg resolution of L. Write
Rⱼ for its chosen projective resolution of Lⱼ and Cⱼ for its chosen cycles resolution. For every
original degree q and n ∈ ℕ, the resolution-degree-(n+1) component of the vertical-homology
augmentation to H_q(L)[0] is zero. -/
@[simp]
theorem rowHomologyAugmentation_f_succ (q n : ℕ) :
    (P.rowHomologyAugmentation q).f (n + 1) = 0 := by
  apply (HomologicalComplex.isZero_single_obj_X
    (ComplexShape.down ℕ) 0 (L.homology q) (n + 1)
      (Nat.succ_ne_zero n)).eq_of_tgt

end CartanEilenbergResolution

end HomologicalComplex

end
