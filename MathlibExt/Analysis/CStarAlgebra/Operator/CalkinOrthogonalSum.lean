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
# Orthogonal block sums in the Calkin algebra

The literal block diagonal of two compact operators is compact. Consequently
the existing block-diagonal star-algebra homomorphism descends to a unital
star-algebra homomorphism from the product of the two Calkin algebras into the
Calkin algebra of their stock orthogonal product.

The quotient carriers, quotient norms and class maps are unchanged. The
construction uses the stock binary quotient eliminator with compact-ideal
compatibility, not a choice of representatives or a second quotient carrier.
The compactness lemma permits incomplete normed spaces and rectangular maps;
the star-algebra map uses complete complex Hilbert spaces, including zero ones.
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

/-- The literal orthogonal block diagonal preserves compactness, without
completeness, inner-product or nontriviality requirements on the spaces. -/
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

/-- Equality of the actual upstairs classes for compact-equivalent representatives. -/
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

/-- The actual unital star-algebra map on the two existing Calkin algebras.
Its computational value uses only public quotient and upstairs class-map DATA. -/
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

/-- The descended map is represented by the literal operator block diagonal. -/
theorem blockDiagonalStarAlgHom_apply (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    blockDiagonalStarAlgHom (classStarMap (H := H) S, classStarMap (H := K) T) =
      classStarMap (H := OrthogonalSum H K) (OrthogonalSum.blockDiagonal S T) :=
  rfl

/-- The canonical simp form acts on the two literal quotient representatives. -/
@[simp]
theorem blockDiagonalStarAlgHom_mk (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    blockDiagonalStarAlgHom
        ((Submodule.Quotient.mk S : CalkinAlgebra ℂ H),
          (Submodule.Quotient.mk T : CalkinAlgebra ℂ K)) =
      (Submodule.Quotient.mk (OrthogonalSum.blockDiagonal S T) :
        CalkinAlgebra ℂ (OrthogonalSum H K)) :=
  rfl

/-- Bundled compatibility with the standard product of the two class maps. -/
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
