/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseUnconditional

/-!
# Unconditional cobase change (the supporting results): tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseUnconditional`:
the vertical-edge identifications for `τ₀` and `τₙ`, the mirror
prism filtration and its attaching horns, the source- and
target-prescribed `Δ[1]`-prism extensions over a cell (including
the degenerate `n = 0` cases with vacuous vertical hypotheses
and concrete low-dimensional instances), the specialness of the
two extremal horns, the implication from inverse `Δ[2]`-prisms to
equivalence of a prism edge, faithfulness of precomposition with
a cobase change granted `2`-simplex correction, and the final
assembly of cobase-change stability against monomorphisms from
the prism strict extension input (A) and `2`-simplex correction
(B2). The two remaining hypotheses of the assembly are pinned
with their full dependent types.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace CobaseUnconditionalTest

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y}
  {j : X ⟶ Y} {C : SSet.{u}}

section VerticalIdentification

/-- The `(0,1)`-edge of `Δ[n+1]` maps under `τ₀` to the vertical
edge at vertex `0`, at a variable universe and at universe `0`,
and concretely for `n = 1, 2`. -/
example (n : ℕ) :
    (SSet.prismTauMap.{u} n 0).app _
        (SSet.stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩
          (Fin.zero_le _)) =
      SSet.prismVertZero n :=
  SSet.prismTauMap_zero_app_edge

example (n : ℕ) :
    (SSet.prismTauMap.{0} n 0).app _
        (SSet.stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩
          (Fin.zero_le _)) =
      SSet.prismVertZero n :=
  SSet.prismTauMap_zero_app_edge

example :
    (SSet.prismTauMap.{u} 1 0).app _
        (SSet.stdSimplex.edge 2 0 ⟨1, by omega⟩ (Fin.zero_le _)) =
      SSet.prismVertZero 1 :=
  SSet.prismTauMap_zero_app_edge

example :
    (SSet.prismTauMap.{u} 2 0).app _
        (SSet.stdSimplex.edge 3 0 ⟨1, by omega⟩ (Fin.zero_le _)) =
      SSet.prismVertZero 2 :=
  SSet.prismTauMap_zero_app_edge

/-- The `(n,n+1)`-edge of `Δ[n+1]` maps under `τₙ` to the
vertical edge at the last vertex. -/
example (n : ℕ) :
    (SSet.prismTauMap.{u} n ⟨n, by omega⟩).app _
        (SSet.stdSimplex.edge (n + 1) ⟨n, by omega⟩
          ⟨n + 1, by omega⟩ (by simp [Fin.le_def])) =
      SSet.prismVertLast n :=
  SSet.prismTauMap_last_app_edge

example :
    (SSet.prismTauMap.{0} 2 ⟨2, by omega⟩).app _
        (SSet.stdSimplex.edge 3 ⟨2, by omega⟩ ⟨3, by omega⟩
          (by simp [Fin.le_def])) =
      SSet.prismVertLast 2 :=
  SSet.prismTauMap_last_app_edge

/-- Values of the two vertical edges, and the boundary
membership of the last vertical. -/
example (n : ℕ) (t : Fin 2) :
    SSet.prodStdSimplex.objEquiv.{u} (SSet.prismVertZero n) t =
      (0, t) :=
  SSet.prismVertZero_objEquiv_apply t

example (n : ℕ) (t : Fin 2) :
    SSet.prodStdSimplex.objEquiv.{u} (SSet.prismVertLast n) t =
      (⟨n, by omega⟩, t) :=
  SSet.prismVertLast_objEquiv_apply t

example (n : ℕ) (hn : 1 ≤ n) :
    SSet.prismVertLast.{u} n ∈ ((∂Δ[n]).prod ⊤).obj _ :=
  SSet.prismVertLast_mem_boundary_prod hn

/-- The constant vertices of the prism and the two degenerate
`n = 0` face computations. -/
example (n : ℕ) (p : Fin (n + 1) × Fin 2) (t : Fin 1) :
    SSet.prodStdSimplex.objEquiv.{u} (SSet.prismVertConst.{u} n p) t =
      p :=
  SSet.prismVertConst_objEquiv_apply.{u} p t

example :
    (Δ[0] ⊗ Δ[1] : SSet.{u}).δ 1 (SSet.prismTau 0 0) =
      SSet.prismVertConst 0 (0, 0) :=
  SSet.prismTau_zero_δ_one

example :
    (Δ[0] ⊗ Δ[1] : SSet.{u}).δ 0 (SSet.prismTau 0 0) =
      SSet.prismVertConst 0 (0, 1) :=
  SSet.prismTau_zero_δ_zero

end VerticalIdentification

section SpecialEdges

/-- The horn lift for `τ₀` sends the `(0,1)`-edge simplex to the
vertical edge, the special edge of the last source horn map is
the vertical image, and the horn is special when the vertical of
the initial datum is an equivalence. -/
example (m : ℕ) :
    (SSet.Subcomplex.hornLift (SSet.prismSrcFilt (m + 1) 1)
        (SSet.prismTau (m + 1) 0) (0 : Fin (m + 2)).castSucc
        (SSet.prismSrcFilt_preimage_prismTauMap
          (0 : Fin (m + 2)))).app _
        (SSet.leftHornEdgeSimplex.{u} m) =
      ⟨SSet.prismVertZero (m + 1),
        SSet.prismVertZero_mem_prismSrcFilt (by omega) 1⟩ :=
  SSet.hornLift_app_leftHornEdgeSimplex m

example (m : ℕ)
    (φ : ((SSet.prismSrcFilt (m + 1) 1 :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    (SSet.leftHornEdge
        (SSet.Subcomplex.hornLift (SSet.prismSrcFilt (m + 1) 1)
            (SSet.prismTau (m + 1) 0) (0 : Fin (m + 2)).castSucc
            (SSet.prismSrcFilt_preimage_prismTauMap
              (0 : Fin (m + 2))) ≫ φ)).edge =
      φ.app _ ⟨SSet.prismVertZero (m + 1),
        SSet.prismVertZero_mem_prismSrcFilt (by omega) 1⟩ :=
  SSet.leftHornEdge_hornLift_comp m φ

example (m : ℕ)
    {φ : ((SSet.prismSrcFilt (m + 1) 1 :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    {φ₀ : ((SSet.prismSrcInitial (m + 1) :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    (hrestr : SSet.Subcomplex.homOfLE
        (SSet.prismSrcInitial_le_prismSrcFilt 1) ≫ φ = φ₀)
    (hVert : (SSet.Edge.mk' (φ₀.app _
        ⟨SSet.prismVertZero (m + 1),
          SSet.prismVertZero_mem_prismSrcInitial
            (by omega)⟩)).IsEquivalence) :
    (SSet.leftHornEdge
        (SSet.Subcomplex.hornLift (SSet.prismSrcFilt (m + 1) 1)
            (SSet.prismTau (m + 1) 0) (0 : Fin (m + 2)).castSucc
            (SSet.prismSrcFilt_preimage_prismTauMap
              (0 : Fin (m + 2))) ≫ φ)).IsEquivalence :=
  SSet.isEquivalence_leftHornEdge_prismSrcStep m hrestr hVert

/-- Mirror: the last edge of the last target horn map is the
vertical image at the last vertex. -/
example (m : ℕ) :
    (SSet.Subcomplex.hornLift (SSet.prismTgtFilt (m + 1) (m + 1))
        (SSet.prismTau (m + 1) ⟨m + 1, by omega⟩)
        (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
        (SSet.prismTgtFilt_preimage_prismTauMap
          (⟨m + 1, by omega⟩ : Fin (m + 2)))).app _
        (SSet.rightHornEdgeSimplex.{u} m) =
      ⟨SSet.prismVertLast (m + 1),
        SSet.prismVertLast_mem_prismTgtFilt (by omega) (m + 1)⟩ :=
  SSet.hornLift_app_rightHornEdgeSimplex m

example (m : ℕ)
    {φ : ((SSet.prismTgtFilt (m + 1) (m + 1) :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    {φ₀ : ((SSet.prismTgtInitial (m + 1) :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    (hrestr : SSet.Subcomplex.homOfLE
        (SSet.prismTgtInitial_le_prismTgtFilt (m + 1)) ≫ φ = φ₀)
    (hVert : (SSet.Edge.mk' (φ₀.app _
        ⟨SSet.prismVertLast (m + 1),
          SSet.prismVertLast_mem_prismTgtInitial
            (by omega)⟩)).IsEquivalence) :
    (SSet.rightHornEdge
        (SSet.Subcomplex.hornLift (SSet.prismTgtFilt (m + 1) (m + 1))
            (SSet.prismTau (m + 1) ⟨m + 1, by omega⟩)
            (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
            (SSet.prismTgtFilt_preimage_prismTauMap
              (⟨m + 1, by omega⟩ : Fin (m + 2))) ≫
          φ)).IsEquivalence :=
  SSet.isEquivalence_rightHornEdge_prismTgtStep m hrestr hVert

/-- The degenerate fillers for the two `n = 0` steps need no
quasicategory and no equivalence hypothesis. -/
example (φ : ((SSet.prismSrcFilt 0 1 :
      (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    ∃ σC : Δ[1] ⟶ C,
      SSet.Subcomplex.hornLift (SSet.prismSrcFilt 0 1) (SSet.prismTau 0 0)
          (0 : Fin 1).castSucc
          (SSet.prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ =
        Λ[1, (0 : Fin 1).castSucc].ι ≫ σC :=
  SSet.exists_degen_filler_prismSrc_zero φ

example (φ : ((SSet.prismTgtFilt 0 0 :
      (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    ∃ σC : Δ[1] ⟶ C,
      SSet.Subcomplex.hornLift (SSet.prismTgtFilt 0 0) (SSet.prismTau 0 0)
          (0 : Fin 1).succ
          (SSet.prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ =
        Λ[1, (0 : Fin 1).succ].ι ≫ σC :=
  SSet.exists_degen_filler_prismTgt_zero φ

end SpecialEdges

section MirrorFiltration

/-- The mirror filtration: initial subcomplex, steps, bottom,
top, and the attaching-horn computation, including concrete
instances. -/
example (n : ℕ) :
    SSet.prismTgtInitial.{u} n =
      SSet.Subcomplex.unionProd ∂Δ[n] (SSet.stdSimplex.face {1}) :=
  rfl

example (n m : ℕ) :
    SSet.prismTgtInitial n ≤ SSet.prismTgtFilt n m :=
  SSet.prismTgtInitial_le_prismTgtFilt m

example (n m : ℕ) (hm : m ≤ n) :
    SSet.prismTgtFilt n (m + 1) = SSet.prismTgtFilt n m ⊔
      SSet.Subcomplex.ofSimplex (SSet.prismTau n ⟨m, by omega⟩) :=
  SSet.prismTgtFilt_succ_eq_sup hm

example (n : ℕ) :
    SSet.prismTgtFilt n 0 = SSet.prismTgtInitial n :=
  SSet.prismTgtFilt_zero

example (n : ℕ) : SSet.prismTgtFilt n (n + 1) = ⊤ :=
  SSet.prismTgtFilt_top

example (n : ℕ) (k : Fin (n + 1)) :
    (SSet.prismTgtFilt n k.val).preimage (SSet.prismTauMap n k) =
      Λ[n + 1, k.succ] :=
  SSet.prismTgtFilt_preimage_prismTauMap k

example :
    (SSet.prismTgtFilt 2 0).preimage (SSet.prismTauMap 2 0) =
      Λ[3, (0 : Fin 3).succ] :=
  SSet.prismTgtFilt_preimage_prismTauMap 0

example (n : ℕ) (hn : 1 ≤ n) :
    SSet.prismVertLast.{u} n ∈ (SSet.prismTgtInitial n).obj _ :=
  SSet.prismVertLast_mem_prismTgtInitial hn

end MirrorFiltration

section PrismExtensionCell

/-- Source-prescribed prism extension over a cell, with the full
dependent type pinned, at a variable universe and at universe
`0`. -/
example :
    ∀ (n : ℕ) {C : SSet.{u}} [SSet.Quasicategory C]
      (φ₀ : ((SSet.prismSrcInitial n :
          (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
      (_hVert : ∀ hn : 1 ≤ n,
        (SSet.Edge.mk' (φ₀.app _
            ⟨SSet.prismVertZero n,
              SSet.prismVertZero_mem_prismSrcInitial hn⟩)).IsEquivalence),
      ∃ F : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ C,
        (SSet.prismSrcInitial n).ι ≫ F = φ₀ :=
  fun _n {_} _ φ₀ hVert ↦
    SSet.exists_extension_of_unionProd_boundary_face_zero φ₀ hVert

example (n : ℕ) {C : SSet.{0}} [SSet.Quasicategory C]
    (φ₀ : ((SSet.prismSrcInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{0}).Subcomplex) : SSet.{0}) ⟶ C)
    (hVert : ∀ hn : 1 ≤ n,
      (SSet.Edge.mk' (φ₀.app _
          ⟨SSet.prismVertZero n,
            SSet.prismVertZero_mem_prismSrcInitial hn⟩)).IsEquivalence) :
    ∃ F : (Δ[n] ⊗ Δ[1] : SSet.{0}) ⟶ C,
      (SSet.prismSrcInitial n).ι ≫ F = φ₀ :=
  SSet.exists_extension_of_unionProd_boundary_face_zero φ₀ hVert

/-- For `n = 0` the vertical hypothesis is vacuous: every map
out of `Δ[0] ⊗ {0}` extends to `Δ[0] ⊗ Δ[1]`, into any
quasicategory, and concretely into a nerve. -/
example {C : SSet.{u}} [SSet.Quasicategory C]
    (φ₀ : ((SSet.prismSrcInitial 0 :
        (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    ∃ F : (Δ[0] ⊗ Δ[1] : SSet.{u}) ⟶ C,
      (SSet.prismSrcInitial 0).ι ≫ F = φ₀ :=
  SSet.exists_extension_of_unionProd_boundary_face_zero φ₀
    (fun hn ↦ by omega)

example (D : Type u) [Category.{u} D]
    (φ₀ : ((SSet.prismSrcInitial 0 :
        (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
      CategoryTheory.nerve D) :
    ∃ F : (Δ[0] ⊗ Δ[1] : SSet.{u}) ⟶ CategoryTheory.nerve D,
      (SSet.prismSrcInitial 0).ι ≫ F = φ₀ :=
  SSet.exists_extension_of_unionProd_boundary_face_zero φ₀
    (fun hn ↦ by omega)

/-- For `n = 1, 2` the source extension needs exactly the single
vertical equivalence. -/
example {C : SSet.{u}} [SSet.Quasicategory C]
    (φ₀ : ((SSet.prismSrcInitial 1 :
        (Δ[1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (SSet.Edge.mk' (φ₀.app _
        ⟨SSet.prismVertZero 1,
          SSet.prismVertZero_mem_prismSrcInitial
            (by omega)⟩)).IsEquivalence) :
    ∃ F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C,
      (SSet.prismSrcInitial 1).ι ≫ F = φ₀ :=
  SSet.exists_extension_of_unionProd_boundary_face_zero φ₀
    (fun _ ↦ hVert)

example {C : SSet.{u}} [SSet.Quasicategory C]
    (φ₀ : ((SSet.prismSrcInitial 2 :
        (Δ[2] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (SSet.Edge.mk' (φ₀.app _
        ⟨SSet.prismVertZero 2,
          SSet.prismVertZero_mem_prismSrcInitial
            (by omega)⟩)).IsEquivalence) :
    ∃ F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ C,
      (SSet.prismSrcInitial 2).ι ≫ F = φ₀ :=
  SSet.exists_extension_of_unionProd_boundary_face_zero φ₀
    (fun _ ↦ hVert)

/-- Target-prescribed prism extension over a cell, with the full
dependent type pinned, and the vacuous `n = 0` and concrete
`n = 1` instances. -/
example :
    ∀ (n : ℕ) {C : SSet.{u}} [SSet.Quasicategory C]
      (φ₀ : ((SSet.prismTgtInitial n :
          (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
      (_hVert : ∀ hn : 1 ≤ n,
        (SSet.Edge.mk' (φ₀.app _
            ⟨SSet.prismVertLast n,
              SSet.prismVertLast_mem_prismTgtInitial hn⟩)).IsEquivalence),
      ∃ F : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ C,
        (SSet.prismTgtInitial n).ι ≫ F = φ₀ :=
  fun _n {_} _ φ₀ hVert ↦
    SSet.exists_extension_of_unionProd_boundary_face_one φ₀ hVert

example {C : SSet.{u}} [SSet.Quasicategory C]
    (φ₀ : ((SSet.prismTgtInitial 0 :
        (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    ∃ F : (Δ[0] ⊗ Δ[1] : SSet.{u}) ⟶ C,
      (SSet.prismTgtInitial 0).ι ≫ F = φ₀ :=
  SSet.exists_extension_of_unionProd_boundary_face_one φ₀
    (fun hn ↦ by omega)

example {C : SSet.{u}} [SSet.Quasicategory C]
    (φ₀ : ((SSet.prismTgtInitial 1 :
        (Δ[1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : (SSet.Edge.mk' (φ₀.app _
        ⟨SSet.prismVertLast 1,
          SSet.prismVertLast_mem_prismTgtInitial
            (by omega)⟩)).IsEquivalence) :
    ∃ F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C,
      (SSet.prismTgtInitial 1).ι ≫ F = φ₀ :=
  SSet.exists_extension_of_unionProd_boundary_face_one φ₀
    (fun _ ↦ hVert)

end PrismExtensionCell

section CompPrisms

/-- Inverse `Δ[2]`-prisms make a prism edge an equivalence, with
the full dependent type pinned. -/
example :
    ∀ {B C : SSet.{u}} {x₀ x₁ : ((ihom B).obj C) _⦋0⦌}
      (F G : B ⊗ Δ[1] ⟶ C)
      (_hF₀ : ((ihom B).obj C).δ 1 (SSet.ihomSimplexOfPrism F) = x₀)
      (_hF₁ : ((ihom B).obj C).δ 0 (SSet.ihomSimplexOfPrism F) = x₁)
      (_hG₀ : ((ihom B).obj C).δ 1 (SSet.ihomSimplexOfPrism G) = x₁)
      (_hG₁ : ((ihom B).obj C).δ 0 (SSet.ihomSimplexOfPrism G) = x₀)
      (P Q : B ⊗ Δ[2] ⟶ C)
      (_hP₂ : (B ◁ SSet.stdSimplex.δ 2) ≫ P = F)
      (_hP₀ : (B ◁ SSet.stdSimplex.δ 0) ≫ P = G)
      (_hP₁ : (B ◁ SSet.stdSimplex.δ 1) ≫ P =
        (B ◁ SSet.stdSimplex.σ 0) ≫ (B ◁ SSet.stdSimplex.δ 1) ≫ F)
      (_hQ₂ : (B ◁ SSet.stdSimplex.δ 2) ≫ Q = G)
      (_hQ₀ : (B ◁ SSet.stdSimplex.δ 0) ≫ Q = F)
      (_hQ₁ : (B ◁ SSet.stdSimplex.δ 1) ≫ Q =
        (B ◁ SSet.stdSimplex.σ 0) ≫ (B ◁ SSet.stdSimplex.δ 1) ≫ G),
      (SSet.edgeOfPrism F _hF₀ _hF₁).IsEquivalence :=
  fun F G hF₀ hF₁ hG₀ hG₁ P Q hP₂ hP₀ hP₁ hQ₂ hQ₀ hQ₁ ↦
    SSet.edgeOfPrism_isEquivalence_of_compPrisms F G hF₀ hF₁ hG₀ hG₁
      P Q hP₂ hP₀ hP₁ hQ₂ hQ₀ hQ₁

end CompPrisms

section FaithfulnessAssembly

/-- The `2`-simplex correction property, with its full dependent
type pinned. -/
example :
    ∀ {E B : SSet.{u}} (_p : E ⟶ B), Prop :=
  fun p ↦ SSet.CompCorrection p

example {E B : SSet.{u}} (p : E ⟶ B)
    (h : ∀ {x₀ x₁ x₂ : E _⦋0⦌} {e₀₁ : SSet.Edge x₀ x₁}
      {e₁₂ : SSet.Edge x₁ x₂} {e₀₂ : SSet.Edge x₀ x₂}
      (_s : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂)
      (t : SSet.Edge.CompStruct (e₀₁.map p) (e₁₂.map p) (e₀₂.map p)),
      ∃ s' : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂,
        p.app _ s'.simplex = t.simplex) :
    SSet.CompCorrection p :=
  h

/-- Faithfulness of precomposition with a cobase change granted
`2`-simplex correction, and cobase-change stability granted (A)
and (B2). -/
example (sq : IsPushout i f f' j)
    (hf : SSet.categoricalEquivalences f) [SSet.Quasicategory C]
    (hCorr : SSet.CompCorrection ((MonoidalClosed.pre i).app C)) :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre f').app C)).toFunctor.Faithful :=
  SSet.hoFunctor_pre_faithful_of_isPushout_of_compCorrection
    sq hf C hCorr

example (sq : IsPushout i f f' j) [Mono i]
    (hf : SSet.categoricalEquivalences f)
    (hA : ∀ (C : SSet.{u}) [SSet.Quasicategory C],
      SSet.HoPrePrismStrictExtension i C)
    (hCorr : ∀ (C : SSet.{u}) [SSet.Quasicategory C],
      SSet.CompCorrection ((MonoidalClosed.pre i).app C)) :
    SSet.categoricalEquivalences f' :=
  SSet.categoricalEquivalences.of_isPushout_of_prismStrictExtension_of_compCorrection
    sq hf hA hCorr

/-- Stability of categorical equivalences under cobase change
against all monomorphisms, granted (A) and (B2) for every
monomorphism: the target instance with its two remaining
hypotheses named. -/
example
    (hA : ∀ {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (C : SSet.{u})
      [SSet.Quasicategory C], SSet.HoPrePrismStrictExtension i C)
    (hCorr : ∀ {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (C : SSet.{u})
      [SSet.Quasicategory C],
      SSet.CompCorrection ((MonoidalClosed.pre i).app C)) :
    SSet.categoricalEquivalences.IsStableUnderCobaseChangeAgainst
      (CategoryTheory.MorphismProperty.monomorphisms SSet.{u}) :=
  SSet.categoricalEquivalences_isStableUnderCobaseChangeAgainst_mono_of_prism_of_correction
    hA hCorr

end FaithfulnessAssembly

end CobaseUnconditionalTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
