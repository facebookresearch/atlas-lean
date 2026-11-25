/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.PrismCobase

/-! Tests for the prism-triangulation infrastructure of packet
T43: range/value formulas for the top simplices of
`Δ[n] ⊗ Δ[1]`, the horn-attachment pushout, the decreasing
filtration steps/top/bottom, and the attaching-horn (preimage)
computation for the source-prescribed prism. -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

section Signatures

variable {n : ℕ} {k : Fin (n + 1)} {i : Fin (n + 2)} {C : SSet.{u}}
  [Quasicategory C]

#check @SSet.prismTau_eq_nonDegenerateEquiv_val
#check @SSet.prismTauMap
#check @SSet.prodStdSimplex₁.ι
#check @SSet.prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₀_iff
#check @SSet.prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₁_iff
#check @SSet.prismTau_objEquiv_fst_val
#check @SSet.prismTau_objEquiv_snd
#check @SSet.mem_range_codimOne_objEquiv
#check @SSet.prismTau_δ_ofSimplex_le_boundary_prod_top_of_lt
#check @SSet.prismTau_δ_ofSimplex_le_boundary_prod_top_of_gt
#check @SSet.prismSrcFilt
#check @SSet.prismSrcFilt_eq_succ_sup
#check @SSet.prismSrcFilt_top
#check @SSet.prismSrcFilt_zero
#check @SSet.prismSrcFilt_preimage_prismTauMap
#check @SSet.prismVertZero_mem_prismSrcInitial

/-- `prismTauMap` is the existing inclusion `prodStdSimplex₁.ι`,
with its monomorphicity instance, and `prismTau` is the
underlying simplex of `nonDegenerateEquiv`. -/
example : prismTauMap.{u} n k = prodStdSimplex₁.ι k := rfl

example : Mono (prismTauMap.{u} n k) := inferInstance

example : prismTau.{u} n k =
    (prodStdSimplex₁.nonDegenerateEquiv k).val :=
  prismTau_eq_nonDegenerateEquiv_val k

end Signatures

section Values

/-- The vertex `(0, 1)` is in the range of `τ₀`, and the vertex
`(5, 0)` is not in the range of `τ₂` over `Δ[5]`, by the range
characterizations of `ProdStdSimplexOneCompat.lean` applied
through `prismTau_eq_nonDegenerateEquiv_val`. -/
example : ((0 : Fin 6), (1 : Fin 2)) ∈
    Set.range (prodStdSimplex.objEquiv.{u} (prismTau 5 0)) := by
  exact
    (prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₁_iff
      0 0).2 (Fin.zero_le _)

example : (⟨5, by omega⟩, (0 : Fin 2)) ∉
    Set.range (prodStdSimplex.objEquiv.{u}
      (prismTau 5 ⟨2, by omega⟩)) := by
  intro h
  have hle :=
    (prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₀_iff
      ⟨2, by omega⟩ ⟨5, by omega⟩).1 h
  exact absurd hle (by decide)

/-- First coordinates of `τ₂` over `Δ[4]` at positions `0,…,5`
are `0,1,2,2,3,4`. -/
example (t : Fin 6) :
    ((prodStdSimplex.objEquiv.{u} (prismTau 4 ⟨2, by omega⟩) t).1).val =
      if t.val ≤ 2 then t.val else t.val - 1 :=
  prismTau_objEquiv_fst_val _ _

/-- The filtration really starts at the initial subcomplex and
ends at the whole prism, at `n = 3`. -/
example : prismSrcFilt.{u} 3 4 = prismSrcInitial 3 :=
  prismSrcFilt_top

example : prismSrcFilt.{u} 3 0 = ⊤ :=
  prismSrcFilt_zero

/-- One step of the filtration at `n = 3`, `m = 1`. -/
example : prismSrcFilt.{u} 3 1 = prismSrcFilt 3 2 ⊔
    Subcomplex.ofSimplex (prismTau 3 ⟨1, by omega⟩) :=
  prismSrcFilt_eq_succ_sup (by omega)

end Values

section AttachingHorn

variable {n : ℕ} (k : Fin (n + 1))

/-- The attaching horn computation, at every `k`. -/
example : (prismSrcFilt n (k.val + 1)).preimage
    (prismTauMap.{u} n k) = Λ[n + 1, k.castSucc] :=
  prismSrcFilt_preimage_prismTauMap k

/-- The resulting attaching square is a pushout, using the
preimage computation and injectivity of `τₖ` on simplices. -/
example : CategoryTheory.IsPushout
    (Subcomplex.hornLift (prismSrcFilt n (k.val + 1)) (prismTau n k)
      k.castSucc (prismSrcFilt_preimage_prismTauMap k))
    Λ[n + 1, k.castSucc].ι
    (Subcomplex.homOfLE le_sup_left)
    (Subcomplex.simplexLiftSup (prismSrcFilt n (k.val + 1))
      (prismTau n k)) :=
  Subcomplex.isPushout_hornAttach (prismSrcFilt_preimage_prismTauMap k)
    (fun h ↦ injective_of_mono _ h)

/-- Extension step in usable form: a map out of `Gₖ₊₁` extends
over `τₖ` once the horn `Λ[n+1, k]` is filled compatibly.
Injectivity of `τₖ` on simplices is the `Mono` instance for
`SSet.prodStdSimplex₁.ι k` (i.e. for `prismTauMap n k`), read
pointwise by `CategoryTheory.injective_of_mono`. -/
example {C : SSet.{u}} [Quasicategory C]
    (φ : ((prismSrcFilt n (k.val + 1) :
      (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (σC : Δ[n + 1] ⟶ C)
    (hσC : Subcomplex.hornLift (prismSrcFilt n (k.val + 1))
        (prismTau n k) k.castSucc
          (prismSrcFilt_preimage_prismTauMap k) ≫ φ =
      Λ[n + 1, k.castSucc].ι ≫ σC) :
    ∃ φ' : ((prismSrcFilt n (k.val + 1) ⊔
          Subcomplex.ofSimplex (prismTau n k) :
            (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C,
      Subcomplex.homOfLE le_sup_left ≫ φ' = φ ∧
        Subcomplex.simplexLiftSup (prismSrcFilt n (k.val + 1))
            (prismTau n k) ≫ φ' = σC := by
  refine Subcomplex.exists_extension_sup_of_horn_filler
    (prismSrcFilt_preimage_prismTauMap k) ?_ φ σC hσC
  intro d s₁ s₂ h
  exact injective_of_mono _ h

/-- The vertical edge at vertex `0` lies in the initial
subcomplex for `n ≥ 1`. -/
example (hn : 1 ≤ n) :
    prismVertZero.{u} n ∈ (prismSrcInitial n).obj _ :=
  prismVertZero_mem_prismSrcInitial hn

end AttachingHorn

end SSet
