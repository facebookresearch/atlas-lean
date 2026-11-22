/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.DescentProp412
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality
public import MathlibExt.AlgebraicTopology.SimplexCategory.ZeroAddSuccIso

/-!
# Horn descent: Remark 3.3, Lemma 4.8 and Proposition 4.11

Notation: `Homᴸ_S(x, y) = S_{x/} ×_S {y}` is the naive (left,
join-slice) mapping space, landed as `SSet.mappingSpaceLeft`; `S`
is *pre-fibrant* (`SSet.IsPreFibrant`, Definition 3.1) if every
`Λ²₁`-horn fills and every inner horn with constant `0`-th face
`d₀` fills.

An `n`-simplex of `Homᴸ_S(x, y)` is an `(n+1)`-simplex `σ` of `S`
with `σ(0) = x` and back face `d₀σ = σ|Δ^{{1,…,n+1}}` the constant
`n`-simplex at `y` (§2.4 of the paper; landed as
`SSet.mappingSpaceLeft.simplexEquivSucc`, with the endpoint maps
transported along `SSet.joinStdSimplexIso 0 n`). The face maps of
`Homᴸ` correspond to `δ₁, …, δ_{n+1}` of `σ`: simplicial operators
act on the right join factor. A horn `Λ[m, i] ⟶ Homᴸ` (`m ≥ 2`) is
a compatible family of `(m-1)`-simplices `f_j` (`j ≠ i`), i.e. of
`m`-simplices `s_j` of `S` with `s_j(0) = x`, `d₀s_j` constant at
`y`, pairwise compatible. Adjoin the constant `m`-simplex at `y`
as face `0`: this is compatible with every `s_j`, because one side
of the compatibility is a face of a constant simplex and the other
is `d₀s_j`. We obtain a horn `Λ[m+1, i+1] ⟶ S` (indices shifted by
one) whose `0`-th face is constant.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial
open scoped CategoryTheory.MonoidalCategory.DayFunctor

universe u

namespace SSet

/-!
## §2. The transported endpoint inclusions are the standard ones

The landed left mapping space is described by simplices over
`Δ[0 + n + 1]` (the unreduced form produced by
`SSet.joinStdSimplexIso 0 n`). Since `0 + n + 1` is only
propositionally equal to `n + 1`, we fix once and for all the
identification `SSet.zeroAddSuccIso n : ⦋0 + n + 1⦌ ≅ ⦋n + 1⦌`
in the simplex category, and read the transported endpoint maps
through it: `SSet.leftVertexSucc n` is vertex `0` of `Δ[n + 1]`
(proved below); `SSet.backInclusionSucc n` is defined by the same
reading, and its identification with `δ₀` is reduced below to
`inr'` followed by the identification being `δ₀` plus the mirror
`joinInr` computation from `JoinNaturality.lean`. This is the agreement between Stevenson's
`(n+1)`-simplex description of `Homᴸ` (§2.4) and the landed join
model.
-/

/-- The left vertex of the join model, read in `Δ[n + 1]`. -/
def leftVertexSucc (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] :=
  leftVertex n ≫ SSet.stdSimplex.map (zeroAddSuccIso n).hom

/-- The back face of the join model, read in `Δ[n + 1]`. -/
def backInclusionSucc (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1] :=
  backInclusion n ≫ SSet.stdSimplex.map (zeroAddSuccIso n).hom

/-- The transported left vertex is `inl'`: this is the supporting results
`SSet.joinInl_comp_joinStdSimplexIso_hom` at `m = 0`. -/
theorem leftVertex_eq (n : ℕ) :
    leftVertex.{u} n =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inl' ⦋0⦌ ⦋n⦌) :=
  joinInl_comp_joinStdSimplexIso_hom 0 n

/-- `inl' ⦋0⦌ ⦋n⦌`, read through `SSet.zeroAddSuccIso`, is the
`0`-th vertex inclusion. -/
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

/-- **`leftVertexSucc` is vertex `0`**: the transported left
endpoint inclusion, read in `Δ[n + 1]`, is the standard vertex
`0` map. -/
theorem leftVertexSucc_eq (n : ℕ) :
    leftVertexSucc.{u} n =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) := by
  rw [leftVertexSucc, leftVertex_eq, ← Functor.map_comp,
    inl'_zero_comp_zeroAddSuccIso_hom]

/-- `inr' ⦋0⦌ ⦋n⦌`, read through `SSet.zeroAddSuccIso`, is the
face map `δ₀`. -/
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

/-- The face `δ₀` composed with `δ (succ j)` is `δ j` composed
with `δ₀` (the case `i = 0` of `SimplexCategory.δ_comp_δ`). -/
lemma δ_zero_comp_δ_succ {n : ℕ} (j : Fin (n + 2)) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ SimplexCategory.δ j.succ =
      SimplexCategory.δ j ≫ SimplexCategory.δ (0 : Fin (n + 3)) := by
  have h := SimplexCategory.δ_comp_δ (n := n) (i := (0 : Fin (n + 2)))
    (j := j) (Fin.zero_le j)
  rwa [Fin.castSucc_zero] at h

/-- `inl' ⦋0⦌ ⦋m⦌` is the constant vertex-`0` map into
`⦋0 + m + 1⦌`. -/
lemma inl'_zero_eq_const (m : ℕ) :
    AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌ =
      SimplexCategory.const ⦋0⦌ ⦋0 + m + 1⦌ 0 := by
  apply SimplexCategory.Hom.ext_zero_left
  apply Fin.ext
  rw [AugmentedSimplexCategory.inl'_eval]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Tensoring a face map with the identity on `⦋0⦌` on the left
is, after the `SSet.zeroAddSuccIso` identifications, the face map
`δ (succ j)`. Proof by `tensorObj_hom_ext`: the `inl`
precomposition is `vertex 0 ≫ δ (succ j) = vertex 0` and the
`inr` precomposition is the simplicial identity
`SSet.δ_zero_comp_δ_succ`. -/
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

/-- The inverse form of `SSet.zeroAddSuccIso_hom_comp_δ_succ`. -/
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
