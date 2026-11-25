/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlternating
public import MathlibExt.AlgebraicTopology.SimplicialObject.Diagonal
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney

/-!
# Degreewise bisimplicial Alexander--Whitney comparison

For a bisimplicial object `B`, this file defines the degreewise
Alexander--Whitney comparison from the alternating-face complex of the
diagonal to the signed total of the alternating bicomplex.  In total degree
`n`, the `(p,q)` summand applies the outer front face and inner back face for
`p+q=n`.

The components are natural in `B`.  The differential identity and resulting
chain map are deliberately deferred to the subsequent cut-face/sign
calculation; no quasi-isomorphism is claimed here.
-/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialAlexanderWhitney

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasFiniteCoproducts A]

/-- Complementary degree of a finite Alexander--Whitney cut. -/
def cutComplement (n : ℕ) (p : Fin (n + 1)) : ℕ :=
  n - (p : ℕ)

/-- The two degrees of an Alexander--Whitney cut add to the total degree. -/
theorem cut_add (n : ℕ) (p : Fin (n + 1)) :
    (p : ℕ) + cutComplement n p = n := by
  unfold cutComplement
  omega

/-- The complement of the canonical cut at `p` in total degree `p+q` is
`q`. -/
theorem cutComplement_add (p q : ℕ) :
    cutComplement (p + q) (⟨p, by omega⟩ : Fin (p + q + 1)) = q := by
  unfold cutComplement
  change p + q - p = q
  omega

/-- The complement of a cut is the displayed second degree whenever the two
degrees add to the total. -/
theorem cutComplement_of_add_eq {p q n : ℕ} (h : p + q = n) :
    cutComplement n (⟨p, by omega⟩ : Fin (n + 1)) = q := by
  subst n
  exact cutComplement_add p q

/-- Alternating-face chain complex of the diagonal of a bisimplicial object. -/
noncomputable abbrev diagonalAlternatingComplex
    (B : SimplicialObject (SimplicialObject A)) : ChainComplex A ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex A).obj
    ((SimplicialObject.diagonalFunctor A).obj B)

omit [Limits.HasFiniteCoproducts A] in
/-- Degree objects of the diagonal alternating complex are the diagonal
bidegrees of the bisimplicial object. -/
@[simp]
theorem diagonalAlternatingComplex_X
    (B : SimplicialObject (SimplicialObject A)) (n : ℕ) :
    (diagonalAlternatingComplex B).X n =
      (B.obj (Opposite.op ⦋n⦌)).obj (Opposite.op ⦋n⦌) :=
  rfl

/-- Inclusion of bidegree `(p,q)` into a specified equal total degree `n`. -/
noncomputable def totalιOfEq
    (B : SimplicialObject (SimplicialObject A))
    (p q n : ℕ) (h : p + q = n) :
    (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).X n :=
  (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
    (ComplexShape.down ℕ) p q n h

/-- Naturality of a bidegree inclusion under a bisimplicial map. -/
theorem totalιOfEq_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    (p q n : ℕ) (h : p + q = n) :
    totalιOfEq B p q n h ≫
        ((AlgebraicTopology.bisimplicialAlternatingTotalComplexFunctor A).map f).f n =
      (f.app (Opposite.op ⦋p⦌)).app (Opposite.op ⦋q⦌) ≫
        totalιOfEq B' p q n h := by
  change (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
      (ComplexShape.down ℕ) p q n h ≫
        (HomologicalComplex₂.total.map
          ((AlgebraicTopology.bisimplicialAlternatingBicomplexFunctor A).map f)
          (ComplexShape.down ℕ)).f n = _
  rw [HomologicalComplex₂.ιTotal_map]
  rfl

/-- Front/back face map from diagonal degree `n` to the bidegree selected by
the cut `p`. -/
noncomputable def faceToBidegree
    (B : SimplicialObject (SimplicialObject A)) (n : ℕ)
    (p : Fin (n + 1)) :
    (diagonalAlternatingComplex B).X n ⟶
      (B.obj (Opposite.op ⦋(p : ℕ)⦌)).obj
        (Opposite.op ⦋cutComplement n p⦌) :=
  ((AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B (cut_add n p)).app (Opposite.op ⦋n⦌)) ≫
    AlgebraicTopology.AlexanderWhitney.backFace
      (B.obj (Opposite.op ⦋(p : ℕ)⦌)) (cut_add n p)

/-- Front/back face map to a named bidegree `(p,q)` in an equal total degree
`n`. -/
noncomputable def faceToBidegreeOfEq
    (B : SimplicialObject (SimplicialObject A))
    (p q n : ℕ) (h : p + q = n) :
    (diagonalAlternatingComplex B).X n ⟶
      (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  ((AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B h).app (Opposite.op ⦋n⦌)) ≫
    AlgebraicTopology.AlexanderWhitney.backFace
      (B.obj (Opposite.op ⦋p⦌)) h

/-- Front/back face map to an explicitly named bidegree `(p,q)`. -/
noncomputable def faceToBidegreeAdd
    (B : SimplicialObject (SimplicialObject A)) (p q : ℕ) :
    (diagonalAlternatingComplex B).X (p + q) ⟶
      (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  faceToBidegreeOfEq B p q (p + q) rfl

omit [Limits.HasFiniteCoproducts A] in
/-- Naturality of the front/back face map for a fixed cut. -/
theorem faceToBidegree_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    (n : ℕ) (p : Fin (n + 1)) :
    ((AlgebraicTopology.alternatingFaceMapComplex A).map
      ((SimplicialObject.diagonalFunctor A).map f)).f n ≫
        faceToBidegree B' n p =
      faceToBidegree B n p ≫
        (f.app (Opposite.op ⦋(p : ℕ)⦌)).app
          (Opposite.op ⦋cutComplement n p⦌) := by
  unfold faceToBidegree
  change (f.app (Opposite.op ⦋n⦌)).app (Opposite.op ⦋n⦌) ≫ _ = _
  have hfront := congrArg
    (fun k => k.app (Opposite.op ⦋n⦌))
    (AlgebraicTopology.AlexanderWhitney.frontFace_naturality f (cut_add n p))
  change (AlgebraicTopology.AlexanderWhitney.frontFace
      (C := SimplicialObject A) B (cut_add n p)).app (Opposite.op ⦋n⦌) ≫
        (f.app (Opposite.op ⦋(p : ℕ)⦌)).app (Opposite.op ⦋n⦌) =
    (f.app (Opposite.op ⦋n⦌)).app (Opposite.op ⦋n⦌) ≫
      (AlgebraicTopology.AlexanderWhitney.frontFace
        (C := SimplicialObject A) B' (cut_add n p)).app
          (Opposite.op ⦋n⦌) at hfront
  have hback := AlgebraicTopology.AlexanderWhitney.backFace_naturality
    (f.app (Opposite.op ⦋(p : ℕ)⦌)) (cut_add n p)
  let front := (AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B (cut_add n p)).app (Opposite.op ⦋n⦌)
  let back' := AlgebraicTopology.AlexanderWhitney.backFace
    (B'.obj (Opposite.op ⦋(p : ℕ)⦌)) (cut_add n p)
  let fp := (f.app (Opposite.op ⦋(p : ℕ)⦌)).app (Opposite.op ⦋n⦌)
  have h₁ := (hfront =≫ back').symm
  have h₂ := Category.assoc front fp back'
  have h₃ := (front ≫= hback).symm
  let hfinal := (Category.assoc _ _ _).symm.trans
    ((h₁.trans (h₂.trans h₃)).trans (Category.assoc _ _ _).symm)
  dsimp only [front, back'] at hfinal
  exact hfinal

omit [HasFiniteCoproducts A] in
/-- Naturality of the equality-indexed front/back face map. -/
theorem faceToBidegreeOfEq_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    (p q n : ℕ) (h : p + q = n) :
    ((AlgebraicTopology.alternatingFaceMapComplex A).map
      ((SimplicialObject.diagonalFunctor A).map f)).f n ≫
        faceToBidegreeOfEq B' p q n h =
      faceToBidegreeOfEq B p q n h ≫
        (f.app (Opposite.op ⦋p⦌)).app (Opposite.op ⦋q⦌) := by
  unfold faceToBidegreeOfEq
  change (f.app (Opposite.op ⦋n⦌)).app (Opposite.op ⦋n⦌) ≫ _ = _
  have hfront := congrArg
    (fun k => k.app (Opposite.op ⦋n⦌))
    (AlgebraicTopology.AlexanderWhitney.frontFace_naturality f h)
  change (AlgebraicTopology.AlexanderWhitney.frontFace
      (C := SimplicialObject A) B h).app (Opposite.op ⦋n⦌) ≫
        (f.app (Opposite.op ⦋p⦌)).app (Opposite.op ⦋n⦌) =
    (f.app (Opposite.op ⦋n⦌)).app (Opposite.op ⦋n⦌) ≫
      (AlgebraicTopology.AlexanderWhitney.frontFace
        (C := SimplicialObject A) B' h).app (Opposite.op ⦋n⦌) at hfront
  have hback := AlgebraicTopology.AlexanderWhitney.backFace_naturality
    (f.app (Opposite.op ⦋p⦌)) h
  let front := (AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B h).app (Opposite.op ⦋n⦌)
  let back' := AlgebraicTopology.AlexanderWhitney.backFace
    (B'.obj (Opposite.op ⦋p⦌)) h
  let fp := (f.app (Opposite.op ⦋p⦌)).app (Opposite.op ⦋n⦌)
  have h₁ := (hfront =≫ back').symm
  have h₂ := Category.assoc front fp back'
  have h₃ := (front ≫= hback).symm
  let hfinal := (Category.assoc _ _ _).symm.trans
    ((h₁.trans (h₂.trans h₃)).trans (Category.assoc _ _ _).symm)
  dsimp only [front, back'] at hfinal
  exact hfinal

/-- The `(p,q)` summand of the degree-`n` bisimplicial
Alexander--Whitney component. -/
noncomputable def summand
    (B : SimplicialObject (SimplicialObject A)) (n : ℕ)
    (p : Fin (n + 1)) :
    (diagonalAlternatingComplex B).X n ⟶
      (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).X n :=
  faceToBidegreeOfEq B (p : ℕ) (cutComplement n p) n (cut_add n p) ≫
    totalιOfEq B (p : ℕ) (cutComplement n p) n (cut_add n p)

/-- Degree-`n` bisimplicial Alexander--Whitney component, summed over all
cuts `p+q=n`. -/
noncomputable def component
    (B : SimplicialObject (SimplicialObject A)) (n : ℕ) :
    (diagonalAlternatingComplex B).X n ⟶
      (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).X n :=
  ∑ p : Fin (n + 1), summand B n p

/-- Expanded finite-sum formula for the degreewise component. -/
theorem component_eq_sum
    (B : SimplicialObject (SimplicialObject A)) (n : ℕ) :
    component B n =
      ∑ p : Fin (n + 1), summand B n p := rfl

/-- Naturality of one finite-cut summand. -/
theorem summand_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    (n : ℕ) (p : Fin (n + 1)) :
    ((AlgebraicTopology.alternatingFaceMapComplex A).map
      ((SimplicialObject.diagonalFunctor A).map f)).f n ≫
        summand B' n p =
      summand B n p ≫
        ((AlgebraicTopology.bisimplicialAlternatingTotalComplexFunctor A).map f).f n := by
  unfold summand
  let d := ((AlgebraicTopology.alternatingFaceMapComplex A).map
    ((SimplicialObject.diagonalFunctor A).map f)).f n
  let a := faceToBidegreeOfEq B (p : ℕ) (cutComplement n p) n (cut_add n p)
  let a' := faceToBidegreeOfEq B' (p : ℕ) (cutComplement n p) n (cut_add n p)
  let t := totalιOfEq B (p : ℕ) (cutComplement n p) n (cut_add n p)
  let t' := totalιOfEq B' (p : ℕ) (cutComplement n p) n (cut_add n p)
  let g := (f.app (Opposite.op ⦋(p : ℕ)⦌)).app
    (Opposite.op ⦋cutComplement n p⦌)
  let T := ((AlgebraicTopology.bisimplicialAlternatingTotalComplexFunctor A).map f).f n
  have ha : d ≫ a' = a ≫ g :=
    faceToBidegreeOfEq_naturality f _ _ _ _
  have ht : t ≫ T = g ≫ t' := totalιOfEq_naturality f _ _ _ _
  exact (Category.assoc d a' t').symm |>.trans
    ((ha =≫ t').trans
      ((Category.assoc a g t').trans
        ((a ≫= ht.symm).trans (Category.assoc a t T).symm)))

/-- Naturality of the degreewise bisimplicial Alexander--Whitney component. -/
theorem component_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex A).map
      ((SimplicialObject.diagonalFunctor A).map f)).f n ≫
        component B' n =
      component B n ≫
        ((AlgebraicTopology.bisimplicialAlternatingTotalComplexFunctor A).map f).f n := by
  simp only [component, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  exact summand_naturality f n p

end AlgebraicTopology.BisimplicialAlexanderWhitney
