/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Operator.Calkin
public import MathlibExt.Analysis.InnerProductSpace.OrthogonalSum
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Orthogonal block sums modulo compacts

For normed spaces over a nontrivially normed field, the rectangular block map `(x,y) ↦ (S x,T
y)` is compact when both component maps are compact. Completeness and inner products are not
required for this assertion.

For complete complex Hilbert spaces `H,K`, the block diagonal descends to a unital complex star
homomorphism `Q(H) × Q(K) → Q(H ⊕ K)`, with value `([S],[T]) ↦ [S ⊕ T]`. The orthogonal sum uses
its two-norm, and the Calkin algebras use their quotient operator norms.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OrthogonalSum

universe u𝕜 uH₁ uK₁ uH₂ uK₂

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {H₁ : Type uH₁} {K₁ : Type uK₁} {H₂ : Type uH₂} {K₂ : Type uK₂}
variable [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [NormedAddCommGroup K₁] [NormedSpace 𝕜 K₁]
variable [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]
variable [NormedAddCommGroup K₂] [NormedSpace 𝕜 K₂]

/-- **Compact rectangular block diagonal.** Let `𝕜` be a nontrivially normed field and
`H₁,K₁,H₂,K₂` normed `𝕜`-spaces. If `S : H₁ →L[𝕜] H₂` and `T : K₁ →L[𝕜] K₂` are compact, then
`(x,y) ↦ (S x,T y)` is compact between their orthogonal two-norm sums; no completeness or
inner product is assumed. -/
theorem isCompactOperator_blockDiagonal (S : H₁ →L[𝕜] H₂) (T : K₁ →L[𝕜] K₂)
    (hS : IsCompactOperator S) (hT : IsCompactOperator T) :
    IsCompactOperator (blockDiagonal S T) := by
  let L := (inl (𝕜 := 𝕜) H₂ K₂).toContinuousLinearMap.comp
    (S.comp (WithLp.fstL 2 𝕜 H₁ K₁))
  let R := (inr (𝕜 := 𝕜) H₂ K₂).toContinuousLinearMap.comp
    (T.comp (WithLp.sndL 2 𝕜 H₁ K₁))
  have hL : IsCompactOperator L := by
    simpa only [L, ContinuousLinearMap.coe_comp] using
      (hS.comp_clm (WithLp.fstL 2 𝕜 H₁ K₁)).clm_comp
        (inl (𝕜 := 𝕜) H₂ K₂).toContinuousLinearMap
  have hR : IsCompactOperator R := by
    simpa only [R, ContinuousLinearMap.coe_comp] using
      (hT.comp_clm (WithLp.sndL 2 𝕜 H₁ K₁)).clm_comp
        (inr (𝕜 := 𝕜) H₂ K₂).toContinuousLinearMap
  have hsum : IsCompactOperator (L + R) := by
    have hcoe :
        ((L + R : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
          OrthogonalSum H₁ K₁ → OrthogonalSum H₂ K₂) =
        (L : OrthogonalSum H₁ K₁ → OrthogonalSum H₂ K₂) +
          (R : OrthogonalSum H₁ K₁ → OrthogonalSum H₂ K₂) := by
      funext x
      exact _root_.add_apply L R x
    exact hcoe.symm ▸ hL.add hR
  have hdiag : blockDiagonal S T = L + R := by
    ext x
    rw [blockDiagonal_apply, _root_.add_apply]
    change WithLp.toLp 2 (S x.fst, T x.snd) =
      inl (𝕜 := 𝕜) H₂ K₂ (S x.fst) + inr (𝕜 := 𝕜) H₂ K₂ (T x.snd)
    exact (inl_fst_add_inr_snd (𝕜 := 𝕜) H₂ K₂
      (WithLp.toLp 2 (S x.fst, T x.snd))).symm
  rw [hdiag]
  exact hsum

end OrthogonalSum

namespace CalkinAlgebra

universe uH uK

variable {H : Type uH} {K : Type uK}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Compact equivalence of block representatives.** For complex Hilbert spaces `H,K`, if `S-S'`
and `T-T'` are compact on their respective spaces, then `[S ⊕ T] = [S' ⊕ T']` in `Q(H ⊕ K)`. -/
private theorem blockDiagonalClass_respects
    (S : H →L[ℂ] H) (T : K →L[ℂ] K) (S' : H →L[ℂ] H) (T' : K →L[ℂ] K)
    (hS : (compactOperator (RingHom.id ℂ) H H).quotientRel S S')
    (hT : (compactOperator (RingHom.id ℂ) K K).quotientRel T T') :
    ((classStarMap (H := OrthogonalSum H K)).comp
        (OrthogonalSum.blockDiagonalStarAlgHom (𝕜 := ℂ) (H := H) (K := K))) (S, T) =
      ((classStarMap (H := OrthogonalSum H K)).comp
        (OrthogonalSum.blockDiagonalStarAlgHom (𝕜 := ℂ) (H := H) (K := K))) (S', T') := by
  let d := (classStarMap (H := OrthogonalSum H K)).comp
    (OrthogonalSum.blockDiagonalStarAlgHom (𝕜 := ℂ) (H := H) (K := K))
  change d (S, T) = d (S', T')
  have hSc : IsCompactOperator (S - S') :=
    (Submodule.quotientRel_def (compactOperator (RingHom.id ℂ) H H)).1 hS
  have hTc : IsCompactOperator (T - T') :=
    (Submodule.quotientRel_def (compactOperator (RingHom.id ℂ) K K)).1 hT
  have hc := OrthogonalSum.isCompactOperator_blockDiagonal (S - S') (T - T') hSc hTc
  have hz := (classStarMap_eq_zero_iff
    (H := OrthogonalSum H K) (OrthogonalSum.blockDiagonal (S - S') (T - T'))).2 hc
  change d ((S, T) - (S', T')) = 0 at hz
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

/-- **Star homomorphism of orthogonal Calkin sums.** For complex Hilbert spaces `H,K`, the map
`Q(H) × Q(K) → Q(H ⊕ K)` is the unital complex star homomorphism represented by `(S,T) ↦ S ⊕
T`. -/
def blockDiagonalStarAlgHom :
    (CalkinAlgebra ℂ H × CalkinAlgebra ℂ K) →⋆ₐ[ℂ]
      CalkinAlgebra ℂ (OrthogonalSum H K) := by
  let d := (classStarMap (H := OrthogonalSum H K)).comp
    (OrthogonalSum.blockDiagonalStarAlgHom (𝕜 := ℂ) (H := H) (K := K))
  let f : CalkinAlgebra ℂ H → CalkinAlgebra ℂ K →
      CalkinAlgebra ℂ (OrthogonalSum H K) :=
    fun x y => Quotient.liftOn₂ x y (fun S T => d (S, T))
      (by exact blockDiagonalClass_respects (H := H) (K := K))
  have hmk : ∀ (S : H →L[ℂ] H) (T : K →L[ℂ] K),
      f (classStarMap (H := H) S) (classStarMap (H := K) T) = d (S, T) := by
    intro S T
    rfl
  exact
    { toFun x := Quotient.liftOn₂ x.1 x.2
        (fun S T => ((classStarMap (H := OrthogonalSum H K)).comp
          (OrthogonalSum.blockDiagonalStarAlgHom (𝕜 := ℂ) (H := H) (K := K))) (S, T))
        (by exact blockDiagonalClass_respects (H := H) (K := K))
      map_zero' := by
        change f 0 0 = 0
        have hf : f 0 0 = d (0, 0) := by
          simpa only [map_zero] using
            hmk (0 : H →L[ℂ] H) (0 : K →L[ℂ] K)
        exact hf.trans (map_zero d)
      map_one' := by
        change f 1 1 = 1
        have hf : f 1 1 = d (1, 1) := by
          simpa only [map_one] using
            hmk (1 : H →L[ℂ] H) (1 : K →L[ℂ] K)
        exact hf.trans (map_one d)
      map_add' := by
        rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
        obtain ⟨S, rfl⟩ := classStarMap_surjective (H := H) x₁
        obtain ⟨T, rfl⟩ := classStarMap_surjective (H := K) x₂
        obtain ⟨U, rfl⟩ := classStarMap_surjective (H := H) y₁
        obtain ⟨V, rfl⟩ := classStarMap_surjective (H := K) y₂
        change f
            (classStarMap (H := H) S + classStarMap (H := H) U)
            (classStarMap (H := K) T + classStarMap (H := K) V) =
          f (classStarMap (H := H) S) (classStarMap (H := K) T) +
            f (classStarMap (H := H) U) (classStarMap (H := K) V)
        rw [← map_add (classStarMap (H := H)) S U,
          ← map_add (classStarMap (H := K)) T V,
          hmk, hmk, hmk]
        exact map_add d (S, T) (U, V)
      map_mul' := by
        rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
        obtain ⟨S, rfl⟩ := classStarMap_surjective (H := H) x₁
        obtain ⟨T, rfl⟩ := classStarMap_surjective (H := K) x₂
        obtain ⟨U, rfl⟩ := classStarMap_surjective (H := H) y₁
        obtain ⟨V, rfl⟩ := classStarMap_surjective (H := K) y₂
        change f
            (classStarMap (H := H) S * classStarMap (H := H) U)
            (classStarMap (H := K) T * classStarMap (H := K) V) =
          f (classStarMap (H := H) S) (classStarMap (H := K) T) *
            f (classStarMap (H := H) U) (classStarMap (H := K) V)
        rw [← map_mul (classStarMap (H := H)) S U,
          ← map_mul (classStarMap (H := K)) T V,
          hmk, hmk, hmk]
        exact map_mul d (S, T) (U, V)
      commutes' c := by
        change f (algebraMap ℂ (CalkinAlgebra ℂ H) c)
            (algebraMap ℂ (CalkinAlgebra ℂ K) c) =
          algebraMap ℂ (CalkinAlgebra ℂ (OrthogonalSum H K)) c
        have hH : classStarMap (H := H) (algebraMap ℂ (H →L[ℂ] H) c) =
            algebraMap ℂ (CalkinAlgebra ℂ H) c :=
          (classStarMap (H := H)).toAlgHom.commutes c
        have hK : classStarMap (H := K) (algebraMap ℂ (K →L[ℂ] K) c) =
            algebraMap ℂ (CalkinAlgebra ℂ K) c :=
          (classStarMap (H := K)).toAlgHom.commutes c
        exact (congrArg₂ f hH.symm hK.symm).trans
          ((hmk (algebraMap ℂ (H →L[ℂ] H) c)
            (algebraMap ℂ (K →L[ℂ] K) c)).trans (d.toAlgHom.commutes c))
      map_star' := by
        rintro ⟨x, y⟩
        obtain ⟨S, rfl⟩ := classStarMap_surjective (H := H) x
        obtain ⟨T, rfl⟩ := classStarMap_surjective (H := K) y
        change f (star (classStarMap (H := H) S))
            (star (classStarMap (H := K) T)) =
          star (f (classStarMap (H := H) S) (classStarMap (H := K) T))
        rw [← map_star (classStarMap (H := H)) S,
          ← map_star (classStarMap (H := K)) T, hmk, hmk]
        exact map_star d (S, T)
    }

/-- **Diagonal Calkin map on operator classes.** For complex Hilbert spaces `H,K`,
`blockDiagonalStarAlgHom ([S],[T]) = [OrthogonalSum.blockDiagonal S T]`. -/
theorem blockDiagonalStarAlgHom_apply (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    blockDiagonalStarAlgHom (classStarMap (H := H) S, classStarMap (H := K) T) =
      classStarMap (H := OrthogonalSum H K) (OrthogonalSum.blockDiagonal S T) :=
  rfl

/-- **Diagonal map on quotient representatives.** For complex Hilbert spaces `H,K`, the pair of
compact-ideal quotient classes of `S,T` is sent to the quotient class of their block diagonal
`S ⊕ T`. -/
@[simp]
theorem blockDiagonalStarAlgHom_mk (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    blockDiagonalStarAlgHom
        ((Submodule.Quotient.mk S : CalkinAlgebra ℂ H),
          (Submodule.Quotient.mk T : CalkinAlgebra ℂ K)) =
      (Submodule.Quotient.mk (OrthogonalSum.blockDiagonal S T) :
        CalkinAlgebra ℂ (OrthogonalSum H K)) :=
  rfl

/-- **Diagonal map and the class projections.** For complex Hilbert spaces `H,K`, the map of
Calkin products satisfies `β ∘ (q_H × q_K) = q_(H⊕K) ∘ diag`, where `β =
blockDiagonalStarAlgHom`. -/
theorem blockDiagonalStarAlgHom_comp_classMaps :
    (blockDiagonalStarAlgHom (H := H) (K := K)).comp
        (((classStarMap (H := H)).comp
            (StarAlgHom.fst ℂ (H →L[ℂ] H) (K →L[ℂ] K))).prod
          ((classStarMap (H := K)).comp
            (StarAlgHom.snd ℂ (H →L[ℂ] H) (K →L[ℂ] K)))) =
      (classStarMap (H := OrthogonalSum H K)).comp
        (OrthogonalSum.blockDiagonalStarAlgHom (𝕜 := ℂ) (H := H) (K := K)) := by
  ext p
  exact blockDiagonalStarAlgHom_apply p.1 p.2

end CalkinAlgebra
