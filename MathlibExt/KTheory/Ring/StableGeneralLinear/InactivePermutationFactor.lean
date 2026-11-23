/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.InactivePermutation
public import MathlibExt.GroupTheory.PerfectNormalClosure
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import MathlibExt.KTheory.Ring.K1.Whitehead
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ClassifyingSpaceFundamentalGroup
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ClassifyingSpacePlusSubgroup
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpace
public import MathlibExt.KTheory.Ring.StableGeneralLinear.StabilizeTo
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# A genuine perfect inactive factor for original permutation differences

The inactive restriction of an even permutation is padded by five
identities, then mapped from its actual alternating group into the original
general-linear group over R. Its image is perfect. A computed block map
places it back in the original ambient coordinates, and the full original
permutation matrix is recovered after ordinary identity stabilization.
The complete active and inactive block groups commute. No finite elementary
intersection, ring commutativity, factor witness, or homotopy is assumed.
-/

set_option autoImplicit false

noncomputable section

open Matrix CategoryTheory

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private theorem permutationUnits_reindex
    {Index₁ Index₂ : Type*}
    [DecidableEq Index₁] [DecidableEq Index₂] [Fintype Index₁] [Fintype Index₂]
    (e : Index₁ ≃ Index₂) (σ : Equiv.Perm Index₁) :
    Matrix.GeneralLinearGroup.reindexMulEquiv e
        (Matrix.GeneralLinearGroup.permutationUnitsHom R Index₁ σ) =
      Matrix.GeneralLinearGroup.permutationUnitsHom R Index₂ (e.permCongr σ) :=
  Matrix.GeneralLinearGroup.permutationUnitsHom_reindex R e σ

private theorem permutationUnits_leftBlock
    (Index₁ Index₂ : Type*) [DecidableEq Index₁] [DecidableEq Index₂]
    [Fintype Index₁] [Fintype Index₂] (σ : Equiv.Perm Index₁) :
    Matrix.GeneralLinearGroup.permutationUnitsHom R (Index₁ ⊕ Index₂)
      (Equiv.sumCongr σ (1 : Equiv.Perm Index₂)) =
    Matrix.GeneralLinearGroup.blockDiagonalOne Index₁ Index₂ R
      (Matrix.GeneralLinearGroup.permutationUnitsHom R Index₁ σ) := by
  rw [Matrix.GeneralLinearGroup.permutationUnitsHom_sumCongr, map_one,
    Matrix.GeneralLinearGroup.blockDiagonalHom_one_right]

private theorem permutationUnits_rightBlock
    (Index₁ Index₂ : Type*) [DecidableEq Index₁] [DecidableEq Index₂]
    [Fintype Index₁] [Fintype Index₂] (σ : Equiv.Perm Index₂) :
    Matrix.GeneralLinearGroup.permutationUnitsHom R (Index₁ ⊕ Index₂)
      (Equiv.sumCongr (1 : Equiv.Perm Index₁) σ) =
    Matrix.GeneralLinearGroup.blockDiagonalRight Index₁ Index₂ R
      (Matrix.GeneralLinearGroup.permutationUnitsHom R Index₂ σ) := by
  rw [Matrix.GeneralLinearGroup.permutationUnitsHom_sumCongr, map_one,
    Matrix.GeneralLinearGroup.blockDiagonalHom_one_left]

variable (N : ℕ) (s : Set (Fin N)) [DecidablePred (· ∈ s)]

private def inactiveIndexEquiv :
    s ⊕ Equiv.Perm.InactivePaddedIndex s ≃ Fin (N + 5) :=
  (Equiv.sumAssoc s {x : Fin N // x ∉ s} (Fin 5)).symm.trans
    ((Equiv.sumCongr (Equiv.sumCompl (fun x : Fin N => x ∈ s))
      (Equiv.refl (Fin 5))).trans (finSumFinEquiv (m := N) (n := 5)))

/-- The original padded inactive alternating group acts by the same
homomorphism of permutation units over the unchanged coefficient ring. -/
public def inactiveAlternatingHom :
    alternatingGroup (Equiv.Perm.InactivePaddedIndex s) →*
      Matrix.GeneralLinearGroup (Equiv.Perm.InactivePaddedIndex s) R :=
  (Matrix.GeneralLinearGroup.permutationUnitsHom R _).comp
    (alternatingGroup (Equiv.Perm.InactivePaddedIndex s)).subtype

private theorem inactiveAlternatingHom_apply_computed
    (σ : alternatingGroup (Equiv.Perm.InactivePaddedIndex s)) :
    inactiveAlternatingHom R N s σ =
      Matrix.GeneralLinearGroup.permutationUnitsHom R _ σ.val := rfl

/-- The actual image of the padded inactive alternating group, with the
original coefficient ring and its original carrier universe. -/
public abbrev inactivePerfectMatrixSubgroup :
    Subgroup (Matrix.GeneralLinearGroup (Equiv.Perm.InactivePaddedIndex s) R) :=
  (inactiveAlternatingHom R N s).range

/-- The carrier of the derived perfect inactive image group. -/
public abbrev InactivePerfectMatrixGroup : Type u :=
  ↥(inactivePerfectMatrixSubgroup R N s)

/-- The image group is genuinely perfect by the existing alternating
commutator theorem and the stock perfect-image theorem. -/
public theorem inactivePerfectMatrixGroup_isPerfect :
    Group.IsPerfect (InactivePerfectMatrixGroup R N s) := by
  letI : Group.IsPerfect (alternatingGroup (Equiv.Perm.InactivePaddedIndex s)) :=
    Equiv.Perm.inactiveAlternating_isPerfect s
  exact Group.IsPerfect.range (inactiveAlternatingHom R N s)

private def inactiveFiniteMatrixHom :
    Matrix.GeneralLinearGroup (Equiv.Perm.InactivePaddedIndex s) R →*
      Matrix.GeneralLinearGroup (Fin (N + 5)) R :=
  (Matrix.GeneralLinearGroup.reindexMulEquiv (inactiveIndexEquiv N s)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.blockDiagonalRight s (Equiv.Perm.InactivePaddedIndex s) R)

/-- The inactive action placed in the original ambient stable matrix
coordinates by the computed index partition. -/
public def inactiveStableMatrixHom :
    Matrix.GeneralLinearGroup (Equiv.Perm.InactivePaddedIndex s) R →* StableGL R :=
  (((StableGL.inclusion (N + 5)).app (SemiRingCat.of R)).hom).comp
    (inactiveFiniteMatrixHom R N s)

/-- The whole original active block has its corresponding literal ambient
action, on the same partition of coordinates. -/
public def activeStableMatrixHom : Matrix.GeneralLinearGroup s R →* StableGL R :=
  (((StableGL.inclusion (N + 5)).app (SemiRingCat.of R)).hom).comp
    ((Matrix.GeneralLinearGroup.reindexMulEquiv (inactiveIndexEquiv N s)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.blockDiagonalOne s (Equiv.Perm.InactivePaddedIndex s) R))

private theorem inactiveIndexEquiv_inl (x : s) :
    inactiveIndexEquiv N s (Sum.inl x) = Fin.castAdd 5 x.val := by
  change (finSumFinEquiv (m := N) (n := 5)) (Sum.inl x.val) = _
  rfl

/-- The literal initial active coordinates in an arbitrary ambient rank. -/
public abbrev initialActiveIndices (n N : ℕ) : Set (Fin N) :=
  {x | x.val < n}

/-- The original finite active index is identified with its actual initial
ambient coordinate; the coefficient ring is unchanged. -/
public def initialActiveIndexEquiv {n N : ℕ} (h : n ≤ N) :
    Fin n ≃ initialActiveIndices n N where
  toFun i := ⟨⟨i.val, i.isLt.trans_le h⟩, i.isLt⟩
  invFun i := ⟨i.val.val, i.property⟩
  left_inv i := Fin.ext rfl
  right_inv i := Subtype.ext (Fin.ext rfl)

/-- Reindexing the full initial active block into its actual ambient
coordinates gives the ORIGINAL StableGL inclusion, even though the
inactive coordinates were enumerated through their genuine complement. -/
public theorem activeStableMatrixHom_initial_apply
    {n N : ℕ} (h : n ≤ N) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    activeStableMatrixHom R N (initialActiveIndices n N)
        (Matrix.GeneralLinearGroup.reindexMulEquiv (initialActiveIndexEquiv h) g) =
      StableGL.of g := by
  let I := Equiv.Perm.InactivePaddedIndex (initialActiveIndices n N)
  let eI : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let e₁ : Fin n ⊕ I ≃ Fin (N + 5) :=
    (Equiv.sumCongr (initialActiveIndexEquiv h) (Equiv.refl I)).trans
      (inactiveIndexEquiv N (initialActiveIndices n N))
  have hcard : n + Fintype.card I = N + 5 := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e₁
  let e₀ : Fin n ⊕ I ≃ Fin n ⊕ Fin (Fintype.card I) :=
    Equiv.sumCongr (Equiv.refl (Fin n)) eI
  let e₂ : Fin n ⊕ I ≃ Fin (N + 5) :=
    (e₀.trans (finSumFinEquiv (m := n) (n := Fintype.card I))).trans (finCongr hcard)
  have hfirst₁ (i : Fin n) : (e₁ (Sum.inl i)).val = i.val := by
    change (inactiveIndexEquiv N (initialActiveIndices n N)
      (Sum.inl (initialActiveIndexEquiv h i))).val = i.val
    rw [inactiveIndexEquiv_inl]
    rfl
  have hfirst₂ (i : Fin n) : (e₂ (Sum.inl i)).val = i.val := by
    rfl
  let d : Equiv.Perm (Fin n ⊕ I) := e₁.trans e₂.symm
  have hd (i : Fin n) : d (Sum.inl i) = Sum.inl i := by
    have hi : e₁ (Sum.inl i) = e₂ (Sum.inl i) :=
      Fin.ext ((hfirst₁ i).trans (hfirst₂ i).symm)
    change e₂.symm (e₁ (Sum.inl i)) = Sum.inl i
    rw [hi, Equiv.symm_apply_apply]
  let gb := Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) I R g
  have hfixed : Matrix.GeneralLinearGroup.reindexMulEquiv d gb = gb :=
    Matrix.GeneralLinearGroup.reindex_blockDiagonalOne_of_fixed_left R d hd g
  have htrans : d.trans e₂ = e₁ := by
    apply Equiv.ext
    intro q
    exact e₂.apply_symm_apply (e₁ q)
  have hchange : Matrix.GeneralLinearGroup.reindexMulEquiv e₁ gb =
      Matrix.GeneralLinearGroup.reindexMulEquiv e₂ gb := by
    have ht : Matrix.GeneralLinearGroup.reindexMulEquiv e₂
        (Matrix.GeneralLinearGroup.reindexMulEquiv d gb) =
        Matrix.GeneralLinearGroup.reindexMulEquiv e₁ gb := by
      apply Units.ext
      have hm := congrArg (fun q : Matrix (Fin n ⊕ I) (Fin n ⊕ I) R ≃
          Matrix (Fin (N + 5)) (Fin (N + 5)) R => q (gb : Matrix _ _ R))
        (Matrix.reindex_trans d d e₂ e₂)
      change Matrix.reindex e₂ e₂ (Matrix.reindex d d (gb : Matrix _ _ R)) =
        Matrix.reindex e₁ e₁ (gb : Matrix _ _ R)
      simpa only [Equiv.trans_apply, htrans] using hm
    exact ht.symm.trans (congrArg
      (Matrix.GeneralLinearGroup.reindexMulEquiv e₂) hfixed)
  have hrefl : Matrix.GeneralLinearGroup.reindexMulEquiv (Equiv.refl (Fin n)) g = g := by
    apply Units.ext
    exact Matrix.reindex_refl_refl _
  have hblocks : Matrix.GeneralLinearGroup.reindexMulEquiv e₀ gb =
      Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin (Fintype.card I)) R g := by
    simpa only [hrefl] using Matrix.GeneralLinearGroup.blockDiagonalOne_reindex R
      (Equiv.refl (Fin n)) eI g
  have hstandard : Matrix.GeneralLinearGroup.reindexMulEquiv e₂ gb =
      Matrix.GeneralLinearGroup.reindexMulEquiv (finCongr hcard)
        (Matrix.GeneralLinearGroup.blockStabilization n (Fintype.card I) R g) := by
    calc
      Matrix.GeneralLinearGroup.reindexMulEquiv e₂ gb =
          Matrix.GeneralLinearGroup.reindexMulEquiv (finCongr hcard)
            (Matrix.GeneralLinearGroup.reindexMulEquiv
              (finSumFinEquiv (m := n) (n := Fintype.card I))
                (Matrix.GeneralLinearGroup.reindexMulEquiv e₀ gb)) := by
        apply Units.ext
        rfl
      _ = _ := by
        rw [hblocks]
        rfl
  have hactive : activeStableMatrixHom R N (initialActiveIndices n N)
      (Matrix.GeneralLinearGroup.reindexMulEquiv (initialActiveIndexEquiv h) g) =
      StableGL.of (Matrix.GeneralLinearGroup.reindexMulEquiv e₁ gb) := by
    change StableGL.of (Matrix.GeneralLinearGroup.reindexMulEquiv
      (inactiveIndexEquiv N (initialActiveIndices n N))
        (Matrix.GeneralLinearGroup.blockDiagonalOne (initialActiveIndices n N) I R
          (Matrix.GeneralLinearGroup.reindexMulEquiv (initialActiveIndexEquiv h) g))) = _
    apply congrArg (fun a : Matrix.GeneralLinearGroup (Fin (N + 5)) R => StableGL.of a)
    rw [← Matrix.GeneralLinearGroup.blockDiagonalOne_reindex R
      (initialActiveIndexEquiv h) (Equiv.refl I) g]
    apply Units.ext
    rfl
  exact hactive.trans ((congrArg (fun a : Matrix.GeneralLinearGroup (Fin (N + 5)) R =>
    StableGL.of a) (hchange.trans hstandard)).trans
      ((StableGL.of_reindex_finCongr hcard _).trans (StableGL.of_blockStabilization g)))

/-- Both complete block groups commute, so their classifying product
family is genuinely defined on all active parameters. -/
public theorem activeInactiveStableMatrix_commute
    (g : Matrix.GeneralLinearGroup s R)
    (h : Matrix.GeneralLinearGroup (Equiv.Perm.InactivePaddedIndex s) R) :
    Commute (activeStableMatrixHom R N s g) (inactiveStableMatrixHom R N s h) := by
  let φ := (((StableGL.inclusion (N + 5)).app (SemiRingCat.of R)).hom).comp
    (Matrix.GeneralLinearGroup.reindexMulEquiv (inactiveIndexEquiv N s)).toMonoidHom
  exact (Matrix.GeneralLinearGroup.commute_blockDiagonalOne_blockDiagonalRight g h).map φ

/-- Every element of the perfect inactive image maps into the SAME stable
elementary subgroup killed by the original BGL plus map. -/
public theorem inactivePerfectMatrixGroup_image_mem
    (h : InactivePerfectMatrixGroup R N s) :
    inactiveStableMatrixHom R N s h.val ∈ stableElementarySubgroup R := by
  letI : Group.IsPerfect (InactivePerfectMatrixGroup R N s) :=
    inactivePerfectMatrixGroup_isPerfect R N s
  have hm := Subgroup.map_le_commutator_of_isPerfect
    (inactivePerfectMatrixSubgroup R N s) (inactiveStableMatrixHom R N s)
  exact commutator_le_stableElementarySubgroup R
    (hm (Subgroup.mem_map_of_mem (inactiveStableMatrixHom R N s) h.property))

/-- The original even inactive permutation gives an actual element of the
derived perfect image group. No matrix-factor witness is a caller input. -/
public def inactivePermutationMatrixFactor (σ : Equiv.Perm (Fin N))
    (hfix : ∀ x ∈ s, σ x = x) (heven : Equiv.Perm.sign σ = 1) :
    InactivePerfectMatrixGroup R N s :=
  ⟨Matrix.GeneralLinearGroup.permutationUnitsHom R _
      (Equiv.Perm.paddedInactivePermutation σ s hfix),
    ⟨⟨Equiv.Perm.paddedInactivePermutation σ s hfix,
      Equiv.Perm.paddedInactivePermutation_even σ s hfix heven⟩,
      inactiveAlternatingHom_apply_computed R N s
        ⟨Equiv.Perm.paddedInactivePermutation σ s hfix,
          Equiv.Perm.paddedInactivePermutation_even σ s hfix heven⟩⟩⟩

private theorem paddedPermutation_reconstruct (σ : Equiv.Perm (Fin N))
    (hfix : ∀ x ∈ s, σ x = x) :
    (inactiveIndexEquiv N s).permCongr
      (Equiv.sumCongr (1 : Equiv.Perm s)
        (Equiv.Perm.paddedInactivePermutation σ s hfix)) =
    (finSumFinEquiv (m := N) (n := 5)).permCongr
      (Equiv.sumCongr σ (1 : Equiv.Perm (Fin 5))) := by
  ext x
  obtain ⟨x, rfl⟩ := (finSumFinEquiv (m := N) (n := 5)).surjective x
  rcases x with x | x
  · by_cases hx : x ∈ s
    · simp [inactiveIndexEquiv, Equiv.permCongr_apply,
        Equiv.sumCompl_symm_apply_of_pos hx, hfix x hx,
        Equiv.Perm.paddedInactivePermutation_eq]
    · simp [inactiveIndexEquiv, Equiv.permCongr_apply,
        Equiv.sumCompl_symm_apply_of_neg hx,
        Equiv.Perm.paddedInactivePermutation_eq, Equiv.Perm.inactiveRestriction_apply]
  · simp [inactiveIndexEquiv, Equiv.permCongr_apply,
      Equiv.Perm.paddedInactivePermutation_eq]

private theorem inactivePermutation_finite_reconstruct (σ : Equiv.Perm (Fin N))
    (hfix : ∀ x ∈ s, σ x = x) :
    inactiveFiniteMatrixHom R N s
        (Matrix.GeneralLinearGroup.permutationUnitsHom R _
          (Equiv.Perm.paddedInactivePermutation σ s hfix)) =
      Matrix.GeneralLinearGroup.blockStabilization N 5 R
        (Matrix.GeneralLinearGroup.permutationUnitsHom R (Fin N) σ) := by
  change Matrix.GeneralLinearGroup.reindexMulEquiv (inactiveIndexEquiv N s)
      (Matrix.GeneralLinearGroup.blockDiagonalRight s (Equiv.Perm.InactivePaddedIndex s) R
        (Matrix.GeneralLinearGroup.permutationUnitsHom R _
          (Equiv.Perm.paddedInactivePermutation σ s hfix))) = _
  rw [← permutationUnits_rightBlock R, permutationUnits_reindex R,
    paddedPermutation_reconstruct N s σ hfix, ← permutationUnits_reindex R,
    permutationUnits_leftBlock R]
  rfl

/-- The computed perfect inactive factor recovers the original ambient
permutation matrix in StableGL, after adding only identity coordinates. -/
public theorem inactivePermutationMatrixFactor_reconstruct (σ : Equiv.Perm (Fin N))
    (hfix : ∀ x ∈ s, σ x = x) (heven : Equiv.Perm.sign σ = 1) :
    inactiveStableMatrixHom R N s (inactivePermutationMatrixFactor R N s σ hfix heven).val =
      StableGL.of (Matrix.GeneralLinearGroup.permutationUnitsHom R (Fin N) σ) := by
  change StableGL.of (inactiveFiniteMatrixHom R N s
    (Matrix.GeneralLinearGroup.permutationUnitsHom R _
      (Equiv.Perm.paddedInactivePermutation σ s hfix))) = _
  exact (congrArg (fun g : Matrix.GeneralLinearGroup (Fin (N + 5)) R => StableGL.of g)
    (inactivePermutation_finite_reconstruct R N s σ hfix)).trans
      (StableGL.of_blockStabilization _)

/-- The original whole active-by-inactive group homomorphism. Its two
images commute by the actual matrix block calculation, not a caller
commutation assumption. -/
public def inactiveClassifyingFamilyHom :
    (Matrix.GeneralLinearGroup s R × InactivePerfectMatrixGroup R N s) →* StableGL R :=
  (activeStableMatrixHom R N s).noncommCoprod
    ((inactiveStableMatrixHom R N s).comp (inactivePerfectMatrixSubgroup R N s).subtype)
      (fun (g : Matrix.GeneralLinearGroup s R) (h : InactivePerfectMatrixGroup R N s) =>
        activeInactiveStableMatrix_commute R N s g h.val)

private theorem inactiveClassifyingFamilyHom_apply_computed
    (g : Matrix.GeneralLinearGroup s R) (h : InactivePerfectMatrixGroup R N s) :
    inactiveClassifyingFamilyHom R N s (g, h) =
      activeStableMatrixHom R N s g * inactiveStableMatrixHom R N s h.val := rfl

/-- Every original active and inactive value has its literal block-product image. -/
public theorem inactiveClassifyingFamilyHom_apply
    (g : Matrix.GeneralLinearGroup s R) (h : InactivePerfectMatrixGroup R N s) :
    inactiveClassifyingFamilyHom R N s (g, h) =
      activeStableMatrixHom R N s g * inactiveStableMatrixHom R N s h.val :=
  inactiveClassifyingFamilyHom_apply_computed R N s g h

/-- At the original active basepoint, the complete inactive perfect group
maps into the actual stable elementary subgroup. -/
public theorem inactiveClassifyingFamilyHom_inactive_mem
    (h : InactivePerfectMatrixGroup R N s) :
    inactiveClassifyingFamilyHom R N s (1, h) ∈ stableElementarySubgroup R := by
  rw [inactiveClassifyingFamilyHom_apply, map_one, one_mul]
  exact inactivePerfectMatrixGroup_image_mem R N s h

/-- The actual classifying functor of the whole commuting active-by-inactive
family. The original opposite convention is retained on both groups. -/
public def inactiveClassifyingFamilyFunctor :
    (SingleObj (Matrix.GeneralLinearGroup s R)ᵐᵒᵖ ×
      SingleObj (InactivePerfectMatrixGroup R N s)ᵐᵒᵖ) ⥤ ClassifyingCategory R where
  obj _ := SingleObj.star (StableGL R)ᵐᵒᵖ
  map g := MulOpposite.op
    (inactiveClassifyingFamilyHom R N s (MulOpposite.unop g.1, MulOpposite.unop g.2))
  map_id _ := by
    change MulOpposite.op (inactiveClassifyingFamilyHom R N s 1) = 1
    rw [map_one]
    rfl
  map_comp f g := by
    apply MulOpposite.unop_injective
    change inactiveClassifyingFamilyHom R N s
        (MulOpposite.unop f.1 * MulOpposite.unop g.1,
          MulOpposite.unop f.2 * MulOpposite.unop g.2) =
      inactiveClassifyingFamilyHom R N s (MulOpposite.unop f.1, MulOpposite.unop f.2) *
        inactiveClassifyingFamilyHom R N s (MulOpposite.unop g.1, MulOpposite.unop g.2)
    simpa only [Prod.mk_mul_mk] using
      (inactiveClassifyingFamilyHom R N s).map_mul
        (MulOpposite.unop f.1, MulOpposite.unop f.2)
        (MulOpposite.unop g.1, MulOpposite.unop g.2)

private theorem inactiveClassifyingFamilyFunctor_map_computed
    {x y : SingleObj (Matrix.GeneralLinearGroup s R)ᵐᵒᵖ ×
      SingleObj (InactivePerfectMatrixGroup R N s)ᵐᵒᵖ} (g : x ⟶ y) :
    (inactiveClassifyingFamilyFunctor R N s).map g =
      MulOpposite.op
        (inactiveClassifyingFamilyHom R N s (MulOpposite.unop g.1, MulOpposite.unop g.2)) := rfl

/-- The full original arrow formula of the parameterized family. -/
public theorem inactiveClassifyingFamilyFunctor_map
    {x y : SingleObj (Matrix.GeneralLinearGroup s R)ᵐᵒᵖ ×
      SingleObj (InactivePerfectMatrixGroup R N s)ᵐᵒᵖ} (g : x ⟶ y) :
    (inactiveClassifyingFamilyFunctor R N s).map g =
      MulOpposite.op
        (inactiveClassifyingFamilyHom R N s (MulOpposite.unop g.1, MulOpposite.unop g.2)) :=
  inactiveClassifyingFamilyFunctor_map_computed R N s g

/-- The normalized opposite/inverse convention for the complete source
family agrees with the original normalized stable matrix loop. -/
public theorem inactiveClassifyingFamilyFunctor_normalized_map
    (g : Matrix.GeneralLinearGroup s R) (h : InactivePerfectMatrixGroup R N s) :
    (inactiveClassifyingFamilyFunctor R N s).map
        (show (SingleObj.star (Matrix.GeneralLinearGroup s R)ᵐᵒᵖ,
            SingleObj.star (InactivePerfectMatrixGroup R N s)ᵐᵒᵖ) ⟶
          (SingleObj.star (Matrix.GeneralLinearGroup s R)ᵐᵒᵖ,
            SingleObj.star (InactivePerfectMatrixGroup R N s)ᵐᵒᵖ) from
              (MulOpposite.op g⁻¹, MulOpposite.op h⁻¹)) =
      MulOpposite.op (inactiveClassifyingFamilyHom R N s (g, h))⁻¹ := by
  rw [inactiveClassifyingFamilyFunctor_map]
  change MulOpposite.op (inactiveClassifyingFamilyHom R N s ((g, h)⁻¹)) = _
  rw [map_inv]

private abbrev initialActiveClassifyingFunctor {n N : ℕ} (h : n ≤ N) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤
      SingleObj (Matrix.GeneralLinearGroup (initialActiveIndices n N) R)ᵐᵒᵖ :=
  (MonoidHom.op
    (Matrix.GeneralLinearGroup.reindexMulEquiv (initialActiveIndexEquiv h)).toMonoidHom).toFunctor

/-- The whole parameter category is the ORIGINAL finite GL_n category,
not a replacement by an unidentified active-coordinate group. The
inactive factor remains the computed perfect image at the ambient rank. -/
public def initialInactiveClassifyingFamilyFunctor {n N : ℕ} (h : n ≤ N) :
    (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ×
      SingleObj (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ) ⥤
        ClassifyingCategory R :=
  ((initialActiveClassifyingFunctor R h).prod
    (𝟭 (SingleObj (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ))) ⋙
      inactiveClassifyingFamilyFunctor R N (initialActiveIndices n N)

/-- Every arrow of the original finite parameter family has the original
stable finite-matrix value and computed inactive image, in their given order. -/
public theorem initialInactiveClassifyingFamilyFunctor_map
    {n N : ℕ} (h : n ≤ N)
    {a b : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ×
      SingleObj (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ}
    (p : a ⟶ b) :
    (initialInactiveClassifyingFamilyFunctor R h).map p =
      MulOpposite.op (StableGL.of (MulOpposite.unop p.1) *
        inactiveStableMatrixHom R N (initialActiveIndices n N) (MulOpposite.unop p.2).val) := by
  change MulOpposite.op (inactiveClassifyingFamilyHom R N (initialActiveIndices n N)
    (Matrix.GeneralLinearGroup.reindexMulEquiv (initialActiveIndexEquiv h)
      (MulOpposite.unop p.1), MulOpposite.unop p.2)) = _
  rw [inactiveClassifyingFamilyHom_apply, activeStableMatrixHom_initial_apply]

/-- The actual whole active restriction is the ORIGINAL finite-to-stable
classifying functor, including every original active arrow. -/
public theorem initialInactiveClassifyingFamily_activeFunctor
    {n N : ℕ} (h : n ≤ N) :
    Prod.sectL (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
        (SingleObj.star (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ) ⋙
      initialInactiveClassifyingFamilyFunctor R h = (finiteToStableCategoryMap R n).toFunctor := by
  apply Functor.hext
  · intro c
    rfl
  · intro c c' p
    apply heq_of_eq
    change (initialInactiveClassifyingFamilyFunctor R h).map
      (p, 𝟙 (SingleObj.star (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ)) = _
    rw [initialInactiveClassifyingFamilyFunctor_map]
    change MulOpposite.op (StableGL.of (MulOpposite.unop p) *
      inactiveStableMatrixHom R N (initialActiveIndices n N) 1) =
      MulOpposite.op (StableGL.of (MulOpposite.unop p))
    rw [map_one, mul_one]

/-- The ORIGINAL plus map kills every original inactive normalized loop.
This is the actual subgroup-killing input for the later whole-family
extension, not an inference of joint nullity from pointwise nullity. -/
public theorem inactiveOriginalLoop_killed {Y : TopCat.{u}}
    (i : ordinaryBGL R ⟶ Y) (y : Y) (hiy : i (ordinaryBGLBasepoint R) = y)
    (hp : TopCat.IsPlusConstructionAt i (ordinaryBGLBasepoint R) y hiy (BGLPlusSubgroup R))
    (h : InactivePerfectMatrixGroup R N s) :
    FundamentalGroup.mapOfEq i.hom hiy
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (ordinaryBGLLoop (inactiveStableMatrixHom R N s h.val)))) = 1 := by
  let w : StableE R :=
    ⟨inactiveStableMatrixHom R N s h.val, inactivePerfectMatrixGroup_image_mem R N s h⟩
  have hm := ordinaryBGLLoop_mem_BGLPlusSubgroup w
  rw [← hp.kernel_eq] at hm
  exact hm

end AlgebraicKTheory.StableGL

end
