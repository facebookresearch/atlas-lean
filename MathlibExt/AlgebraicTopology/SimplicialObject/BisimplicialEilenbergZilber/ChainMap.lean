/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.DifferentialZero
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney.DifferentialExpansion

/-!
# The bisimplicial shuffle chain map

The positive and two zero-boundary shuffle identities cover every bidegree.
Extensionality of the direct-sum total object therefore promotes the
degreewise shuffle components to a natural chain map from the signed total
alternating complex to alternating chains on the diagonal.
-/

@[expose] public section

open CategoryTheory Simplicial SimplexCategory
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

section Total

variable [Limits.HasFiniteCoproducts A]

theorem component_comm (n : ℕ) :
    component B (n + 1) ≫
        (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).d
          (n + 1) n =
      (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).d
          (n + 1) n ≫ component B n := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  change p + q = n + 1 at h
  rw [totalι_comp_component_assoc]
  change _ =
    AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq B p q (n + 1) h ≫
      (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).d (n + 1) n ≫
        component B n
  conv_rhs => rw [← Category.assoc]
  unfold AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq
  rw [AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq_comp_d]
  unfold AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq
  simp only [Preadditive.add_comp]
  rcases p with _ | p
  · rcases q with _ | q
    · omega
    · have hn : n = 0 + q := by omega
      subst n
      have hh : h = rfl := Subsingleton.elim _ _
      cases hh
      simp only [dite_eq_left True.intro, dite_eq_right (Nat.succ_ne_zero q),
        Limits.zero_comp, zero_add, Nat.succ_sub_one, pow_zero, one_smul,
        Category.assoc, totalι_comp_component,
        AlgebraicTopology.bisimplicialAlternatingBicomplex_vertical_d,
        AlgebraicTopology.alternatingFaceMapComplex_obj_d,
        eqToHom_refl, Category.comp_id, Category.id_comp]
      exact shuffleBidegree_comp_objD_left_zero B q
  · rcases q with _ | q
    · have hn : n = p := by omega
      subst n
      have hh : h = rfl := Subsingleton.elim _ _
      cases hh
      simp only [dite_eq_right (Nat.succ_ne_zero p), dite_eq_left True.intro,
        Limits.zero_comp, add_zero, Nat.succ_sub_one, Category.assoc,
        totalι_comp_component,
        AlgebraicTopology.bisimplicialAlternatingBicomplex_horizontal_d_f,
        AlgebraicTopology.alternatingFaceMapComplex_obj_d,
        eqToHom_refl, Category.comp_id, Category.id_comp]
      exact shuffleBidegree_comp_objD_right_zero B p
    · have hn : n = (p + 1) + q := by omega
      subst n
      have hh : h = rfl := Subsingleton.elim _ _
      cases hh
      simp only [dite_eq_right (Nat.succ_ne_zero p),
        dite_eq_right (Nat.succ_ne_zero q), Nat.succ_sub_one,
        Category.assoc, totalι_comp_component, Preadditive.zsmul_comp,
        AlgebraicTopology.bisimplicialAlternatingBicomplex_vertical_d,
        AlgebraicTopology.bisimplicialAlternatingBicomplex_horizontal_d_f,
        AlgebraicTopology.alternatingFaceMapComplex_obj_d,
        eqToHom_refl, Category.comp_id, Category.id_comp]
      exact shuffleBidegree_comp_objD_positive B p q

/-- The bisimplicial shuffle chain map from the signed total alternating
complex to alternating chains on the diagonal. -/
noncomputable def alternatingMap :
    AlgebraicTopology.bisimplicialAlternatingTotalComplex A B ⟶
      AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B where
  f := component B
  comm' := fun {i j} hij => by
    subst hij
    exact component_comm B j

@[simp]
theorem alternatingMap_f (n : ℕ) :
    (alternatingMap B).f n = component B n := rfl

/-- Naturality of the bisimplicial shuffle chain map. -/
@[reassoc]
theorem alternatingMap_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B') :
    (AlgebraicTopology.bisimplicialAlternatingTotalComplexFunctor A).map f ≫
        alternatingMap B' =
      alternatingMap B ≫
        (AlgebraicTopology.alternatingFaceMapComplex A).map
          ((SimplicialObject.diagonalFunctor A).map f) := by
  ext n
  exact component_naturality f n

end Total

end AlgebraicTopology.BisimplicialEilenbergZilber
