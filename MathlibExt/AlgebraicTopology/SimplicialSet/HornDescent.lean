/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.DescentProp412
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality
public import MathlibExt.AlgebraicTopology.SimplexCategory.ZeroAddSuccIso

/-!
# Join vertices and shifted cofaces of standard simplices

For every natural n and universe u, the join Δ[0]⋆Δ[n] is identified with Δ[0+n+1], and the
ordinal isomorphism e_n:[0+n+1]≅[n+1] identifies its left vertex with vertex 0 and its back
inclusion with δ₀. Acting on the right join factor by δ_j shifts the coface index to j+1 in
Δ[n+1].

The module records these vertex and coface equations, including both directions of the e_n
transport. They describe the coordinate maps used in join mapping spaces.

For context on join mapping spaces, see D. Stevenson, Notes on the Joyal model structure,
arXiv:1810.05233.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial
open scoped CategoryTheory.MonoidalCategory.DayFunctor

universe u

namespace SSet

/-!
## The left vertex and back face

Under e_n:[0+n+1]≅[n+1], the ordinal left inclusion [0]→[0+n+1] becomes the constant vertex-0
map, and the right inclusion [n]→[0+n+1] becomes δ₀. The induced standard-simplex maps give the
corresponding simplicial vertex and back-face inclusions in every universe.
-/

/-- For n∈ℕ and simplicial-set universe u, let ℓ_n:Δ[0]→Δ[0+n+1] be the left vertex transported from
Δ[0]⋆Δ[n], and let e_n:[0+n+1]≅[n+1] be the ordinal isomorphism. Define the map Δ[0]→Δ[n+1] as
ℓ_n≫Δ(e_n.hom). It is the successor-simplex presentation of the left join vertex. -/
def leftVertexSucc (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] :=
  leftVertex n ≫ SSet.stdSimplex.map (zeroAddSuccIso n).hom

/-- For n∈ℕ and simplicial-set universe u, let b_n:Δ[n]→Δ[0+n+1] be the right inclusion transported
from Δ[0]⋆Δ[n], and let e_n:[0+n+1]≅[n+1]. Define the map Δ[n]→Δ[n+1] as b_n≫Δ(e_n.hom), giving
the back-face presentation of the join inclusion. -/
def backInclusionSucc (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1] :=
  backInclusion n ≫ SSet.stdSimplex.map (zeroAddSuccIso n).hom

/-- For every n∈ℕ and universe u, the transported left vertex ℓ_n:Δ[0]→Δ[0+n+1] equals the
standard-simplex map induced by the ordinal join inclusion inl′:[0]→[0+n+1]. -/
theorem leftVertex_eq (n : ℕ) :
    leftVertex.{u} n =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inl' ⦋0⦌ ⦋n⦌) :=
  joinInl_comp_joinStdSimplexIso_hom 0 n

/-- For n∈ℕ, let e_n:[0+n+1]≅[n+1] be the order-preserving identification. The ordinal join
inclusion satisfies inl′_{[0],[n]}≫e_n.hom=const_\{[0],[n+1]\}(0). Both sides are maps [0]→[n+1]
in the simplex category. -/
lemma inl'_zero_comp_zeroAddSuccIso_hom (n : ℕ) :
    AugmentedSimplexCategory.inl' ⦋0⦌ ⦋n⦌ ≫ (zeroAddSuccIso n).hom =
      SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0 := by
  apply SimplexCategory.Hom.ext_zero_left
  apply Fin.ext
  have h1 : (AugmentedSimplexCategory.inl' ⦋0⦌ ⦋n⦌ ≫
        (zeroAddSuccIso n).hom).toOrderHom 0 =
      ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋n⦌).toOrderHom 0).cast
        (by omega : 0 + n + 1 + 1 = n + 1 + 1) := rfl
  rw [h1, AugmentedSimplexCategory.inl'_eval]
  simp

/-- For every n∈ℕ and simplicial-set universe u, the map Δ[0]→Δ[n+1] obtained from the left join
vertex through e_n:[0+n+1]≅[n+1] equals Δ(const_{[0],[n+1]}(0)), the standard vertex-0
inclusion. -/
theorem leftVertexSucc_eq (n : ℕ) :
    leftVertexSucc.{u} n =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) := by
  rw [leftVertexSucc, leftVertex_eq, ← Functor.map_comp,
    inl'_zero_comp_zeroAddSuccIso_hom]

/-- For n∈ℕ and e_n:[0+n+1]≅[n+1], inr′_{[0],[n]}≫e_n.hom=δ₀:[n]→[n+1]. Thus the ordinal right
factor occupies vertices 1,…,n+1. -/
lemma inr'_zero_comp_zeroAddSuccIso_hom (n : ℕ) :
    AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌ ≫ (zeroAddSuccIso n).hom =
      SimplexCategory.δ (0 : Fin (n + 2)) := by
  ext i : 3
  apply Fin.ext
  have hδ : (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom i =
      Fin.succ i := by
    change Fin.succAbove 0 i = Fin.succ i
    rw [Fin.succAbove_zero]
  rw [hδ]
  have h1 : (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌ ≫
        (zeroAddSuccIso n).hom).toOrderHom i =
      ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌).toOrderHom i).cast
        (by omega : 0 + n + 1 + 1 = n + 1 + 1) := rfl
  rw [h1, AugmentedSimplexCategory.inr'_eval]
  simp

/-- For n∈ℕ and j∈Fin(n+2), the simplex-category maps satisfy δ₀≫δ_{j+1}=δ_j≫δ₀ as maps [n]→[n+2].
On the left δ₀ has target [n+1], and on the right the final δ₀ has target [n+2]. -/
lemma δ_zero_comp_δ_succ {n : ℕ} (j : Fin (n + 2)) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ SimplexCategory.δ j.succ =
      SimplexCategory.δ j ≫ SimplexCategory.δ (0 : Fin (n + 3)) := by
  have h := SimplexCategory.δ_comp_δ (n := n) (i := (0 : Fin (n + 2)))
    (j := j) (Fin.zero_le j)
  rwa [Fin.castSucc_zero] at h

/-- For every m∈ℕ, the ordinal join inclusion inl′_{[0],[m]}:[0]→[0+m+1] equals the constant map at
vertex 0 of [0+m+1]. -/
lemma inl'_zero_eq_const (m : ℕ) :
    AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌ =
      SimplexCategory.const ⦋0⦌ ⦋0 + m + 1⦌ 0 := by
  apply SimplexCategory.Hom.ext_zero_left
  apply Fin.ext
  rw [AugmentedSimplexCategory.inl'_eval]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For n∈ℕ, j∈Fin(n+2) and e_n:[0+n+1]≅[n+1], e_n.hom≫δ_{j+1}=(id_[0]⋆δ_j)≫e_{n+1}.hom. Here
id_[0]⋆δ_j is the ordinal join map [0+n+1]→[0+(n+1)+1], so both sides go to [n+2]. -/
lemma zeroAddSuccIso_hom_comp_δ_succ {n : ℕ} (j : Fin (n + 2)) :
    (zeroAddSuccIso n).hom ≫ SimplexCategory.δ j.succ =
      AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋0⦌)
          (SimplexCategory.δ j) ≫
        (zeroAddSuccIso (n + 1)).hom := by
  have key : (𝟙 (WithInitial.of ⦋0⦌) ⊗ₘ
        Join.ofHom (SimplexCategory.δ j)) =
      Join.ofHom (zeroAddSuccIso n).hom ≫
        Join.ofHom (SimplexCategory.δ j.succ) ≫
          Join.ofHom (zeroAddSuccIso (n + 1)).inv := by
    apply AugmentedSimplexCategory.tensorObj_hom_ext
    · rw [AugmentedSimplexCategory.inl_comp_tensorHom, Category.id_comp]
      change AugmentedSimplexCategory.inl' ⦋0⦌ ⦋n + 1⦌ =
        AugmentedSimplexCategory.inl' ⦋0⦌ ⦋n⦌ ≫ (zeroAddSuccIso n).hom ≫
          SimplexCategory.δ j.succ ≫ (zeroAddSuccIso (n + 1)).inv
      rw [inl'_zero_eq_const, inl'_zero_eq_const, SimplexCategory.const_comp]
      congr 1
    · rw [AugmentedSimplexCategory.inr_comp_tensorHom]
      change SimplexCategory.δ j ≫
            AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n + 1⦌ =
          AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌ ≫ (zeroAddSuccIso n).hom ≫
            SimplexCategory.δ j.succ ≫ (zeroAddSuccIso (n + 1)).inv
      have h1 : AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n + 1⦌ =
          SimplexCategory.δ (0 : Fin (n + 3)) ≫
            (zeroAddSuccIso (n + 1)).inv := by
        rw [← inr'_zero_comp_zeroAddSuccIso_hom (n + 1)]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [h1]
      simp only [← Category.assoc]
      rw [inr'_zero_comp_zeroAddSuccIso_hom, δ_zero_comp_δ_succ]
  have hdown : AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋0⦌)
        (SimplexCategory.δ j) =
      (zeroAddSuccIso n).hom ≫ SimplexCategory.δ j.succ ≫
        (zeroAddSuccIso (n + 1)).inv :=
    congrArg WithInitial.down key
  rw [hdown]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- For n∈ℕ, j∈Fin(n+2) and e_n:[0+n+1]≅[n+1], e_n.inv≫(id_[0]⋆δ_j)=δ_{j+1}≫e_{n+1}.inv. The common
source is [n+1] and target [0+(n+1)+1]. -/
lemma zeroAddSuccIso_inv_comp_tensorHomOf_id_δ {n : ℕ} (j : Fin (n + 2)) :
    (zeroAddSuccIso n).inv ≫
        AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋0⦌)
          (SimplexCategory.δ j) =
      SimplexCategory.δ j.succ ≫ (zeroAddSuccIso (n + 1)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, zeroAddSuccIso_hom_comp_δ_succ,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/- The general Day left-unitor API is in JoinNaturality. -/

end SSet

end
