/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialMap
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.Shuffle

/-!
# Bisimplicial shuffle components

For a bidegree `(p,q)`, every `(p,q)`-shuffle supplies an outer degeneracy
from degree `p` to degree `p+q` and an inner degeneracy from degree `q` to
degree `p+q`.  Their signed sum maps the `(p,q)` object of a bisimplicial
object to its diagonal object in degree `p+q`.

Using the generic total-complex descender, these bidegree maps assemble into
a degreewise map from the signed alternating total complex to alternating
chains on the diagonal.  The maps are natural in the bisimplicial object.
The differential identity is proved separately.
-/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasFiniteCoproducts A]
  (B : SimplicialObject (SimplicialObject A))

/-- The unsigned map associated to one shuffle, applying the outer
degeneracy first and then the inner degeneracy. -/
noncomputable def shuffleMap {p q : ℕ}
    (s : AlgebraicTopology.EilenbergZilber.Shuffle p q) :
    (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (p + q) :=
  AlgebraicTopology.Bisimplicial.map B s.leftHom s.rightHom

/-- The signed map associated to one shuffle, applying the outer degeneracy
first and then the inner degeneracy. -/
noncomputable def shuffleSummand {p q : ℕ}
    (s : AlgebraicTopology.EilenbergZilber.Shuffle p q) :
    (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (p + q) :=
  AlgebraicTopology.EilenbergZilber.shuffleSignZ s • shuffleMap B s

/-- The signed sum over all shuffles from bidegree `(p,q)` to diagonal
degree `p+q`. -/
noncomputable def shuffleBidegree (p q : ℕ) :
    (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (p + q) :=
  ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q, shuffleSummand B s

omit [Limits.HasFiniteCoproducts A] in
/-- Naturality of an unsigned bisimplicial shuffle map. -/
theorem shuffleMap_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    {p q : ℕ} (s : AlgebraicTopology.EilenbergZilber.Shuffle p q) :
    shuffleMap B s ≫
        (f.app (Opposite.op ⦋p + q⦌)).app (Opposite.op ⦋p + q⦌) =
      (f.app (Opposite.op ⦋p⦌)).app (Opposite.op ⦋q⦌) ≫
        shuffleMap B' s := by
  unfold shuffleMap
  exact AlgebraicTopology.Bisimplicial.map_naturality f s.leftHom s.rightHom

omit [Limits.HasFiniteCoproducts A] in
/-- Naturality of a single bisimplicial shuffle summand. -/
theorem shuffleSummand_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    {p q : ℕ} (s : AlgebraicTopology.EilenbergZilber.Shuffle p q) :
    shuffleSummand B s ≫
        (f.app (Opposite.op ⦋p + q⦌)).app (Opposite.op ⦋p + q⦌) =
      (f.app (Opposite.op ⦋p⦌)).app (Opposite.op ⦋q⦌) ≫
        shuffleSummand B' s := by
  unfold shuffleSummand
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  congr 1
  exact shuffleMap_naturality f s

omit [Limits.HasFiniteCoproducts A] in
/-- Naturality of the signed bidegree shuffle map. -/
theorem shuffleBidegree_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    (p q : ℕ) :
    shuffleBidegree B p q ≫
        (f.app (Opposite.op ⦋p + q⦌)).app (Opposite.op ⦋p + q⦌) =
      (f.app (Opposite.op ⦋p⦌)).app (Opposite.op ⦋q⦌) ≫
        shuffleBidegree B' p q := by
  simp only [shuffleBidegree, Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact shuffleSummand_naturality f s

/-- The degree-`n` bisimplicial shuffle component, obtained from the
bidegree maps by the universal property of the total coproduct. -/
noncomputable def component (n : ℕ) :
    (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).X n ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n :=
  (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).totalDesc
    (fun p q h =>
      shuffleBidegree B p q ≫ eqToHom (by
        change p + q = n at h
        subst n
        rfl))

/-- Restriction of the degreewise shuffle component to one total-complex
bidegree summand. -/
@[reassoc (attr := simp)]
theorem totalι_comp_component (p q n : ℕ) (h : p + q = n) :
    (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
        (ComplexShape.down ℕ) p q n h ≫ component B n =
      shuffleBidegree B p q ≫ eqToHom (by subst n; rfl) := by
  apply HomologicalComplex₂.ι_totalDesc

/-- Naturality of the degreewise bisimplicial shuffle component. -/
theorem component_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    (n : ℕ) :
    ((AlgebraicTopology.bisimplicialAlternatingTotalComplexFunctor A).map f).f n ≫
        component B' n =
      component B n ≫
        ((AlgebraicTopology.alternatingFaceMapComplex A).map
          ((SimplicialObject.diagonalFunctor A).map f)).f n := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  change p + q = n at h
  subst n
  rw [← Category.assoc]
  change
    (AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq B p q (p + q) rfl ≫
        ((AlgebraicTopology.bisimplicialAlternatingTotalComplexFunctor A).map f).f
          (p + q)) ≫ component B' (p + q) =
      AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq B p q (p + q) rfl ≫
        component B (p + q) ≫
          ((AlgebraicTopology.alternatingFaceMapComplex A).map
            ((SimplicialObject.diagonalFunctor A).map f)).f (p + q)
  rw [AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq_naturality]
  let fpq := (f.app (Opposite.op ⦋p⦌)).app (Opposite.op ⦋q⦌)
  let d := ((AlgebraicTopology.alternatingFaceMapComplex A).map
    ((SimplicialObject.diagonalFunctor A).map f)).f (p + q)
  have ht' := totalι_comp_component B' p q (p + q) rfl
  have ht := totalι_comp_component B p q (p + q) rfl
  simp only [eqToHom_refl, Category.comp_id] at ht' ht
  change (fpq ≫ AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq
      B' p q (p + q) rfl) ≫ component B' (p + q) =
    AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq
      B p q (p + q) rfl ≫ component B (p + q) ≫ d
  calc
    _ = fpq ≫ (AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq
        B' p q (p + q) rfl ≫ component B' (p + q)) := Category.assoc _ _ _
    _ = fpq ≫ shuffleBidegree B' p q := fpq ≫= ht'
    _ = shuffleBidegree B p q ≫ d := by
      dsimp only [fpq, d]
      simpa only [AlgebraicTopology.alternatingFaceMapComplex_map_f,
        SimplicialObject.diagonalFunctor_map_app] using
        (shuffleBidegree_naturality f p q).symm
    _ = (AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq
        B p q (p + q) rfl ≫ component B (p + q)) ≫ d := ht.symm =≫ d
    _ = _ := Category.assoc _ _ _

end AlgebraicTopology.BisimplicialEilenbergZilber
