/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.NondegenerateEmbedding
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Nondegenerate simplices outside a horn

The complement of `Λ^k[d+1]` among the nondegenerate simplices of
`Δ[d+1]` consists of exactly two simplices: the top simplex in degree
`d+1` and the missing `k`th face in degree `d`.

This file exposes that coefficient-independent combinatorics for reuse by
constant- and variable-coefficient normalized-chain calculations. It makes
no chain-complex, homology, anodyne, or model-category claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

/-- The unique top-dimensional nondegenerate simplex of `Δ[d+1]`. -/
noncomputable def hornTopNonDegenerate (d : ℕ) :
    (Δ[d + 1] : SSet.{u}).nonDegenerate (d + 1) :=
  ⟨SSet.stdSimplex.objEquiv.symm (𝟙 _),
    SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate (d + 1)⟩

/-- The nondegenerate `k`th face omitted from `Λ^k[d+1]`. -/
noncomputable def hornMissingFaceNonDegenerate
    (d : ℕ) (k : Fin (d + 2)) :
    (Δ[d + 1] : SSet.{u}).nonDegenerate d :=
  ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ k),
    (SSet.stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono
      (SimplexCategory.δ k)).2 (by infer_instance)⟩

/-- The top simplex is not a simplex of the horn. -/
theorem hornTopNonDegenerate_not_mem
    (d : ℕ) (k : Fin (d + 2)) :
    (hornTopNonDegenerate d).val ∉
      (SSet.horn (d + 1) k).obj _ := by
  exact SSet.objEquiv_symm_notMem_horn_of_isIso k (𝟙 _)

/-- The missing face is not a simplex of the horn. -/
theorem hornMissingFaceNonDegenerate_not_mem
    (d : ℕ) (k : Fin (d + 2)) :
    (hornMissingFaceNonDegenerate d k).val ∉
      (SSet.horn (d + 1) k).obj _ := by
  exact (SSet.objEquiv_symm_δ_notMem_horn_iff k k).2 rfl

/-- A nondegenerate simplex outside `Λ^k[d+1]` has degree `d` or `d+1`. -/
theorem horn_nonDegenerate_outside_dimension
    (d : ℕ) (k : Fin (d + 2)) {q : ℕ}
    (x : (Δ[d + 1] : SSet.{u}).nonDegenerate q)
    (hx : x.val ∉ (SSet.horn (d + 1) k).obj _) :
    q = d ∨ q = d + 1 := by
  have hqle : q ≤ d + 1 :=
    (Δ[d + 1] : SSet.{u}).dim_le_of_nonDegenerate x (d + 1)
  by_contra h
  have hq : q < d := by omega
  apply hx
  rw [SSet.horn_obj_eq_univ k q (by omega)]
  simp

/-- Every top-dimensional nondegenerate simplex of `Δ[d+1]` is the
canonical top simplex. -/
theorem horn_nonDegenerate_outside_eq_top
    (d : ℕ)
    (x : (Δ[d + 1] : SSet.{u}).nonDegenerate (d + 1)) :
    x = hornTopNonDegenerate d := by
  apply Subtype.ext
  simpa [SSet.stdSimplex.nonDegenerate_top_dim,
    hornTopNonDegenerate] using x.property

/-- Every degree-`d` nondegenerate simplex outside the horn is its canonical
missing face. -/
theorem horn_nonDegenerate_outside_eq_missingFace
    (d : ℕ) (k : Fin (d + 2))
    (x : (Δ[d + 1] : SSet.{u}).nonDegenerate d)
    (hx : x.val ∉ (SSet.horn (d + 1) k).obj _) :
    x = hornMissingFaceNonDegenerate d k := by
  let f := SSet.stdSimplex.objEquiv x.val
  let _ : Mono f :=
    (SSet.stdSimplex.mem_nonDegenerate_iff_mono x.val).1 x.property
  obtain ⟨i, hi⟩ := SimplexCategory.eq_δ_of_mono f
  have hval : x.val =
      SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) := by
    calc
      x.val = SSet.stdSimplex.objEquiv.symm f :=
        (SSet.stdSimplex.objEquiv.symm_apply_apply x.val).symm
      _ = _ := by rw [hi]
  have hi_eq : i = k := by
    apply (SSet.objEquiv_symm_δ_notMem_horn_iff i k).1
    intro hmem
    apply hx
    rw [hval]
    exact hmem
  subst i
  apply Subtype.ext
  exact hval

/-- For the horn inclusion, a target nondegenerate simplex is in the range
of the nondegenerate-simplex embedding exactly when its underlying simplex
lies in the horn. -/
theorem mem_range_nonDegenerateEmbedding_horn_iff
    (d : ℕ) (k : Fin (d + 2)) {q : ℕ}
    (x : (Δ[d + 1] : SSet.{u}).nonDegenerate q) :
    x ∈ Set.range
        (SSet.nonDegenerateEmbeddingOfMono
          (SSet.horn (d + 1) k).ι q) ↔
      x.val ∈ (SSet.horn (d + 1) k).obj _ := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.val.property
  · intro hx
    let y₀ : (SSet.horn (d + 1) k).obj _ := ⟨x.val, hx⟩
    have hy₀ : y₀ ∈ (SSet.horn (d + 1) k : SSet.{u}).nonDegenerate q :=
      (SSet.nonDegenerate_iff_of_mono
        (SSet.horn (d + 1) k).ι y₀).1 x.property
    let y : (SSet.horn (d + 1) k : SSet.{u}).nonDegenerate q :=
      ⟨y₀, hy₀⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    rfl

/-- Negated form of `mem_range_nonDegenerateEmbedding_horn_iff`. -/
theorem not_mem_range_nonDegenerateEmbedding_horn_iff
    (d : ℕ) (k : Fin (d + 2)) {q : ℕ}
    (x : (Δ[d + 1] : SSet.{u}).nonDegenerate q) :
    x ∉ Set.range
        (SSet.nonDegenerateEmbeddingOfMono
          (SSet.horn (d + 1) k).ι q) ↔
      x.val ∉ (SSet.horn (d + 1) k).obj _ := by
  simpa only [not_iff_not] using
    mem_range_nonDegenerateEmbedding_horn_iff d k x

end SSet
