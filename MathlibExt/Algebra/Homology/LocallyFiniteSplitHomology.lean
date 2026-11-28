/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologyMapComponent
public import MathlibExt.CategoryTheory.Linear.LocallyFiniteSplitCoproduct
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Finite splitting formulas for coproducts of homology objects

Let C be an abelian category, K and F_j complexes of arbitrary common
shape, and i_j : F_j → K, p_j : K → F_j chain maps with
p_j i_j = id_(F_j) and p_k i_j = 0 for j ≠ k.
Fix a degree n and a bound N ∈ ℕ such that (p_j)_n = 0 for j > N and
∑_(j=0)^N (i_j)_n(p_j)_n = id_(K_n).

If the coproduct of the selected objects H_n(F_j) exists, their homology
inclusions give ⨁_j H_n(F_j) ≅ H_n(K). The inverse is the finite sum
∑_(j=0)^N ι_j ∘ H_n(p_j), and the forward map has components H_n(i_j).
The support and completeness conditions are needed only in the selected
degree n. No preservation-of-coproducts assumption for homology is
required, and all category and index universes remain independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι}
  (K : HomologicalComplex C c) (F : ℕ → HomologicalComplex C c)
  (i : ∀ j : ℕ, F j ⟶ K) (p : ∀ j : ℕ, K ⟶ F j)
  (hsplit : ∀ j : ℕ, i j ≫ p j = 𝟙 (F j))
  (hcross : ∀ j k : ℕ, j ≠ k → i j ≫ p k = 0)
  (n : ι) (N : ℕ)
  (hsupport : ∀ j : ℕ, N < j → (p j).f n = 0)
  (hsum : (∑ j : Fin (N + 1), (p j).f n ≫ (i j).f n) = 𝟙 (K.X n))
  [HasCoproduct (fun j : ℕ => (F j).homology n)]

include hsum in
/-- For complexes F_j,K of any common shape in an abelian
category C, let i_j : F_j → K and p_j : K → F_j be chain maps.
If ∑_(j=0)^N (i_j)_n(p_j)_n = id_(K_n), then
∑_(j=0)^N H_n(i_j) ∘ H_n(p_j) = id_(H_n(K)).
This conclusion uses only the finite sum identity in degree n. -/
theorem finiteSplitHomology_projector_sum :
    (∑ j : Fin (N + 1), homologyMap (p j.val) n ≫ homologyMap (i j.val) n) = 𝟙 (K.homology n) := by
  classical
  let s : K ⟶ K := ∑ j : Fin (N + 1), p j.val ≫ i j.val
  have hs : s.f n = 𝟙 (K.X n) :=
    ((HomologicalComplex.eval C c n).map_sum
      (fun j : Fin (N + 1) => p j.val ≫ i j.val) Finset.univ).trans
        ((Finset.sum_congr rfl (fun j _ => by
          exact HomologicalComplex.comp_f (p j.val) (i j.val) n)).trans hsum)
  have hhom := homologyMap_eq_id_of_component n s hs
  simp_rw [← homologyMap_comp]
  change (∑ j : Fin (N + 1), (homologyFunctor C c n).map (p j.val ≫ i j.val)) = _
  rw [← Functor.map_sum]
  exact hhom

include hsplit hcross hsupport hsum in
/-- In an abelian category C, let chain maps i_j : F_j → K
and p_j : K → F_j split orthogonally. At a fixed degree n assume
(p_j)_n = 0 for j > N and
∑_(j=0)^N (i_j)_n(p_j)_n = id_(K_n), and assume the coproduct
of H_n(F_j) exists. Then ⨁_j H_n(F_j) ≅ H_n(K), with forward
components H_n(i_j) and inverse ∑_(j=0)^N ι_j ∘ H_n(p_j). -/
def finiteSplitHomologyCoproductIso : (∐ (fun j : ℕ => (F j).homology n)) ≅ K.homology n :=
  finiteSplitCoproductIso (fun j : ℕ => (F j).homology n)
    (fun j => homologyMap (i j) n) (fun j => homologyMap (p j) n) N
    (by
      intro j
      rw [← homologyMap_comp, hsplit, homologyMap_id])
    (by
      intro j k hjk
      rw [← homologyMap_comp, hcross j k hjk, homologyMap_zero])
    (by
      intro j hj
      exact homologyMap_eq_zero_of_component n (p j) (hsupport j hj))
    (finiteSplitHomology_projector_sum K F i p n N hsum)

include hsplit hcross hsupport hsum in
/-- For the finite splitting data on complexes F_j,K in an
abelian category, with support bound N and complete projector sum
in degree n, the forward map ⨁_j H_n(F_j) → H_n(K) has jth
component H_n(i_j). The assumed coproduct is only that of the
selected homology objects H_n(F_j). -/
theorem finiteSplitHomologyCoproductIso_hom :
    (finiteSplitHomologyCoproductIso K F i p hsplit hcross n N hsupport hsum).hom =
      Sigma.desc (fun j => homologyMap (i j) n) := rfl

end HomologicalComplex
