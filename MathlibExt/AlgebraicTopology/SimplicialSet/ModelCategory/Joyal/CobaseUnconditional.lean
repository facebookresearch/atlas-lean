/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.PrismCobase

/-!
# Unconditional cobase change along monomorphisms (the supporting results)

This module attacks the four remaining items (i)–(iv) recorded in
the header of `PrismCobase.lean` (lines 29–39 there) together with
the additional comparison obligation (faithfulness), towards the unconditional statement

```text
(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{u}).
```
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

/-!
## The vertical edge of `τ₀` (§1 of the header)

The `(0,1)`-edge of `Δ[n+1]` maps under `τ₀` to `prismVertZero`,
and the `(n,n+1)`-edge maps under `τₙ` to the vertical edge at
vertex `n`. Through `Subcomplex.hornLift_ι` these identify the special
edges of the two extremal attaching horns.
-/

section PrismVerticalIdentification

variable {n : ℕ}

/-- Values of the vertical edge at vertex `0` through
`prodStdSimplex.objEquiv`: at position `t` it is `(0, t)`. -/
lemma prismVertZero_objEquiv_apply (t : Fin 2) :
    prodStdSimplex.objEquiv.{u} (prismVertZero n) t = (0, t) :=
  rfl

/-- The vertical edge of the prism at the last vertex `n`: the
`1`-simplex `(n,0) ⟶ (n,1)`. This is the special edge of the
last attaching horn `Λ[n+1, n+1]` of the mirror filtration. -/
noncomputable def prismVertLast (n : ℕ) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋1⦌ :=
  prodStdSimplex.objEquiv.symm
    ⟨fun t ↦ (⟨n, by omega⟩, t), fun _ _ hab ↦ ⟨le_rfl, hab⟩⟩

/-- Values of the vertical edge at vertex `n` through
`prodStdSimplex.objEquiv`. -/
lemma prismVertLast_objEquiv_apply (t : Fin 2) :
    prodStdSimplex.objEquiv.{u} (prismVertLast n) t =
      (⟨n, by omega⟩, t) :=
  rfl

lemma prismVertLast_fst_apply (t : Fin 2) :
    (prismVertLast n).1 t = ⟨n, by omega⟩ :=
  rfl

/-- The image of the `(0,1)`-edge of `Δ[n+1]` under `τ₀` is the
vertical edge at vertex `0`: at positions `0` and `1`, the chain
`τ₀` takes the values `(0,0)` and `(0,1)` by
`prismTau_objEquiv_fst_val`/`prismTau_objEquiv_snd` at `k = 0`. -/
lemma prismTauMap_zero_app_edge :
    (prismTauMap.{u} n 0).app _
        (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _)) =
      prismVertZero n := by
  have hpos : ∀ t : Fin 2, ((stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩
          (Fin.zero_le _))).toOrderHom t).val = t.val := fun t ↦ by
    fin_cases t <;> rfl
  have h1 : stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _) =
      stdSimplex.objEquiv.symm
        (stdSimplex.objEquiv
          (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _))) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [h1, prismTauMap, prodStdSimplex₁.ι_def,
    yonedaEquiv_symm_app_objEquiv_symm]
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [prodStdSimplex.objEquiv_map_apply, prismVertZero_objEquiv_apply]
  have ht : t.val = 0 ∨ t.val = 1 := by have h2 := t.isLt; omega
  have ht2 := t.isLt
  apply Prod.ext
  · apply Fin.ext
    have h := prismTau_objEquiv_fst_val.{u} (n := n)
      (k := (0 : Fin (n + 1))) (t := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩
          (Fin.zero_le _))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    change (if t.val ≤ 0 then t.val else t.val - 1) = 0
    split_ifs <;> omega
  · have h := prismTau_objEquiv_snd.{u} (n := n)
      (k := (0 : Fin (n + 1))) (t := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩
          (Fin.zero_le _))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    rcases ht with h0 | h0 <;> simp [h0, Fin.ext_iff]

/-- The image of the `(n,n+1)`-edge of `Δ[n+1]` under `τₙ` is the
vertical edge at vertex `n`: at positions `n` and `n+1`, the chain
`τₙ` takes the values `(n,0)` and `(n,1)`. -/
lemma prismTauMap_last_app_edge :
    (prismTauMap.{u} n ⟨n, by omega⟩).app _
        (stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by simp [Fin.le_def])) =
      prismVertLast n := by
  have hpos : ∀ t : Fin 2, ((stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by simp [Fin.le_def]))).toOrderHom t).val = n + t.val :=
    fun t ↦ by fin_cases t <;> rfl
  have h1 :
      stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by simp [Fin.le_def]) =
        stdSimplex.objEquiv.symm
          (stdSimplex.objEquiv
            (stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
              (by simp [Fin.le_def]))) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [h1, prismTauMap, prodStdSimplex₁.ι_def,
    yonedaEquiv_symm_app_objEquiv_symm]
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [prodStdSimplex.objEquiv_map_apply, prismVertLast_objEquiv_apply]
  have ht : t.val = 0 ∨ t.val = 1 := by have h2 := t.isLt; omega
  have ht2 := t.isLt
  apply Prod.ext
  · apply Fin.ext
    have h := prismTau_objEquiv_fst_val.{u} (n := n)
      (k := (⟨n, by omega⟩ : Fin (n + 1))) (t := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by simp [Fin.le_def]))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    change (if n + t.val ≤ n then n + t.val else n + t.val - 1) = n
    split_ifs <;> omega
  · have h := prismTau_objEquiv_snd.{u} (n := n)
      (k := (⟨n, by omega⟩ : Fin (n + 1))) (t := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by simp [Fin.le_def]))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    rcases ht with h0 | h0 <;> simp [h0, Fin.ext_iff]

/-- The vertical edge at vertex `n` lies in `∂Δ[n] ⊗ Δ[1]` for
`n ≥ 1`: its first components miss the value `0`. -/
lemma prismVertLast_mem_boundary_prod (hn : 1 ≤ n) :
    prismVertLast.{u} n ∈ ((∂Δ[n]).prod ⊤).obj _ :=
  ofSimplex_le_prod_top_of_fst_mem
    (mem_boundary_of_forall_ne _ ⟨0, by omega⟩ (fun t ht ↦ by
      rw [prismVertLast_fst_apply] at ht
      have hval := congrArg Fin.val ht
      change n = 0 at hval
      omega)) _
    (Subcomplex.mem_ofSimplex_obj _)

end PrismVerticalIdentification

/-!
## The special edges of the extremal attaching horns

Through `Subcomplex.hornLift_ι`, the `(0,1)`-edge of the last
source-filtration horn map is the image of `prismVertZero`, and
the last edge of the last mirror-filtration horn map is the image
of `prismVertLast`.
-/

section PrismSpecialEdges

variable {n : ℕ} {C : SSet.{u}}

/-- The constant vertex of the prism at `p : Fin (n+1) × Fin 2`. -/
noncomputable def prismVertConst (n : ℕ) (p : Fin (n + 1) × Fin 2) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋0⦌ :=
  prodStdSimplex.objEquiv.symm (OrderHom.const (Fin 1) p)

/-- Values of the constant vertex through `prodStdSimplex.objEquiv`. -/
lemma prismVertConst_objEquiv_apply (p : Fin (n + 1) × Fin 2)
    (t : Fin 1) :
    prodStdSimplex.objEquiv.{u} (prismVertConst n p) t = p :=
  rfl

/-- The vertical edge at vertex `0` lies in every stage of the
source filtration. -/
lemma prismVertZero_mem_prismSrcFilt (hn : 1 ≤ n) (m : ℕ) :
    prismVertZero.{u} n ∈ (prismSrcFilt n m).obj _ :=
  (prismSrcInitial_le_prismSrcFilt m) _
    (prismVertZero_mem_prismSrcInitial hn)

/-- The horn lift for `τ₀` sends the `(0,1)`-edge simplex of
`Λ[m+2, 0]` to the vertical edge at vertex `0`. -/
lemma hornLift_app_leftHornEdgeSimplex (m : ℕ) :
    (Subcomplex.hornLift (prismSrcFilt (m + 1) 1) (prismTau (m + 1) 0)
        (0 : Fin (m + 2)).castSucc
        (prismSrcFilt_preimage_prismTauMap (0 : Fin (m + 2)))).app _
        (leftHornEdgeSimplex.{u} m) =
      ⟨prismVertZero (m + 1),
        prismVertZero_mem_prismSrcFilt (by omega) 1⟩ := by
  apply Subtype.ext
  calc ((Subcomplex.hornLift (prismSrcFilt (m + 1) 1) (prismTau (m + 1) 0)
          (0 : Fin (m + 2)).castSucc
          (prismSrcFilt_preimage_prismTauMap
            (0 : Fin (m + 2)))).app _
          (leftHornEdgeSimplex.{u} m)).val
      = (prismTauMap.{u} (m + 1) 0).app _
          (stdSimplex.edge (m + 2) 0 ⟨1, by omega⟩ (Fin.zero_le _)) :=
        congr($(Subcomplex.hornLift_ι
          (prismSrcFilt_preimage_prismTauMap (0 : Fin (m + 2)))).app _
            (leftHornEdgeSimplex.{u} m))
    _ = prismVertZero (m + 1) := prismTauMap_zero_app_edge

/-- The `(0,1)`-edge of the last source-filtration horn map is
the image of the vertical edge at vertex `0`. -/
lemma leftHornEdge_hornLift_comp (m : ℕ)
    (φ : ((prismSrcFilt (m + 1) 1 :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    (leftHornEdge
        (Subcomplex.hornLift (prismSrcFilt (m + 1) 1) (prismTau (m + 1) 0)
            (0 : Fin (m + 2)).castSucc
            (prismSrcFilt_preimage_prismTauMap
              (0 : Fin (m + 2))) ≫ φ)).edge =
      φ.app _ ⟨prismVertZero (m + 1),
        prismVertZero_mem_prismSrcFilt (by omega) 1⟩ :=
  congrArg (φ.app _) (hornLift_app_leftHornEdgeSimplex m)

/-- The last source-filtration horn is special as soon as the
vertical edge at vertex `0` of the initial datum is an
equivalence. -/
lemma isEquivalence_leftHornEdge_prismSrcStep (m : ℕ)
    {φ : ((prismSrcFilt (m + 1) 1 :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    {φ₀ : ((prismSrcInitial (m + 1) :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    (hrestr : Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt 1) ≫
        φ = φ₀)
    (hVert : (Edge.mk' (φ₀.app _ ⟨prismVertZero (m + 1),
        prismVertZero_mem_prismSrcInitial (by omega)⟩)).IsEquivalence) :
    (leftHornEdge
        (Subcomplex.hornLift (prismSrcFilt (m + 1) 1) (prismTau (m + 1) 0)
            (0 : Fin (m + 2)).castSucc
            (prismSrcFilt_preimage_prismTauMap
              (0 : Fin (m + 2))) ≫ φ)).IsEquivalence := by
  refine (Edge.isEquivalence_iff_of_edge_eq (e :=
      leftHornEdge _) (e' := Edge.mk' (φ₀.app _
        ⟨prismVertZero (m + 1),
          prismVertZero_mem_prismSrcInitial (by omega)⟩)) ?_).2 hVert
  rw [leftHornEdge_hornLift_comp]
  exact congr($(hrestr).app _ ⟨prismVertZero (m + 1),
    prismVertZero_mem_prismSrcInitial (by omega)⟩)

/-- The `δ 1` face of `τ₀` over `Δ[0]` is the vertex `(0,0)`. -/
lemma prismTau_zero_δ_one :
    (Δ[0] ⊗ Δ[1] : SSet.{u}).δ 1 (prismTau 0 0) =
      prismVertConst 0 (0, 0) := by
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [prism_objEquiv_δ_apply, prismVertConst_objEquiv_apply]
  fin_cases t
  apply Prod.ext
  · apply Fin.ext
    have h := prismTau_objEquiv_fst_val.{u} (n := 0)
      (k := (0 : Fin 1)) (t := (1 : Fin 2).succAbove ⟨0, by omega⟩)
    have hpos : ((1 : Fin 2).succAbove ⟨0, by omega⟩).val = 0 := rfl
    rw [hpos] at h
    change ((prodStdSimplex.objEquiv.{u} (prismTau 0 0)
      ((1 : Fin 2).succAbove ⟨0, by omega⟩)).1).val = 0
    rw [h]
    simp
  · have h := prismTau_objEquiv_snd.{u} (n := 0)
      (k := (0 : Fin 1)) (t := (1 : Fin 2).succAbove ⟨0, by omega⟩)
    have hpos : ((1 : Fin 2).succAbove ⟨0, by omega⟩).val = 0 := rfl
    rw [hpos] at h
    rw [h]
    simp

/-- The constant vertex `(0,0)` lies in the source initial
subcomplex over `Δ[0]`: its second coordinate is `0`. -/
lemma prismVertConst_zero_zero_mem_prismSrcInitial :
    prismVertConst.{u} 0 (0, 0) ∈ (prismSrcInitial 0).obj _ := by
  refine (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl ?_)
  rw [stdSimplex.mem_face_iff]
  intro i
  exact Finset.mem_singleton.2 rfl

/-- **The degenerate filler for the `n = 0` source step**: over
`Δ[0]`, the horn `Λ[1, 0]` induced by any map out of
`prismSrcFilt 0 1` is filled by the degenerate edge at the image
of the vertex `(0,0)`. No quasicategory or equivalence hypothesis
is used. -/
lemma exists_degen_filler_prismSrc_zero
    (φ : ((prismSrcFilt 0 1 :
        (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    ∃ σC : Δ[1] ⟶ C,
      Subcomplex.hornLift (prismSrcFilt 0 1) (prismTau 0 0)
          (0 : Fin 1).castSucc
          (prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ =
        Λ[1, (0 : Fin 1).castSucc].ι ≫ σC := by
  set memF : prismVertConst.{u} 0 (0, 0) ∈ (prismSrcFilt 0 1).obj _ :=
    (prismSrcInitial_le_prismSrcFilt 1) _
      prismVertConst_zero_zero_mem_prismSrcInitial with hmemF
  set pt : ((prismSrcFilt 0 1 :
      (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) _⦋0⦌ :=
    ⟨prismVertConst 0 (0, 0), memF⟩ with hpt
  set x₀ : C _⦋0⦌ := φ.app _ pt with hx₀
  refine ⟨yonedaEquiv.symm (C.σ 0 x₀), ?_⟩
  have hι : horn.ι (0 : Fin 1).castSucc (1 : Fin 2) (by decide) ≫
        Subcomplex.hornLift (prismSrcFilt 0 1) (prismTau 0 0)
          (0 : Fin 1).castSucc
          (prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) =
      yonedaEquiv.symm pt := by
    rw [← cancel_mono (prismSrcFilt 0 1).ι]
    have e1 : horn.ι (0 : Fin 1).castSucc (1 : Fin 2) (by decide) ≫
          Subcomplex.hornLift (prismSrcFilt 0 1) (prismTau 0 0)
            (0 : Fin 1).castSucc
            (prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) ≫
          (prismSrcFilt 0 1).ι =
        yonedaEquiv.symm ((Δ[0] ⊗ Δ[1] : SSet.{u}).δ 1 (prismTau 0 0)) := by
      -- `hhl` is `Subcomplex.hornLift_ι` at the preimage
      -- computation, with its type ascribed in the goal's form:
      -- `prismTauMap` is now the (semireducible) def
      -- `prodStdSimplex₁.ι`, so the bare `hornLift_ι` rewrite no
      -- longer matches the goal at reducible transparency.
      have hhl : Subcomplex.hornLift (prismSrcFilt 0 1)
            (prismTau 0 0) (0 : Fin 1).castSucc
            (prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) ≫
          (prismSrcFilt 0 1).ι =
        Λ[1, (0 : Fin 1).castSucc].ι ≫
          yonedaEquiv.symm (prismTau 0 0) :=
        Subcomplex.hornLift_ι
          (prismSrcFilt_preimage_prismTauMap (0 : Fin 1))
      rw [hhl, ← Category.assoc, horn.ι_ι,
        stdSimplex.δ_comp_yonedaEquiv_symm]
    have e2 : yonedaEquiv.symm pt ≫
          (prismSrcFilt 0 1).ι =
        yonedaEquiv.symm (prismVertConst 0 (0, 0)) := by
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
      rfl
    rw [Category.assoc, e1, e2, prismTau_zero_δ_one]
  have hmaps : horn.ι (0 : Fin 1).castSucc (1 : Fin 2) (by decide) ≫
        (Subcomplex.hornLift (prismSrcFilt 0 1) (prismTau 0 0)
            (0 : Fin 1).castSucc
            (prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ) =
      horn.ι (0 : Fin 1).castSucc (1 : Fin 2) (by decide) ≫
        (Λ[1, (0 : Fin 1).castSucc].ι ≫
          yonedaEquiv.symm (C.σ 0 x₀)) := by
    have eL : horn.ι (0 : Fin 1).castSucc (1 : Fin 2) (by decide) ≫
          (Subcomplex.hornLift (prismSrcFilt 0 1) (prismTau 0 0)
              (0 : Fin 1).castSucc
              (prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ) =
        yonedaEquiv.symm x₀ := by
      rw [← Category.assoc, hι]
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact hx₀.symm
    have eR : horn.ι (0 : Fin 1).castSucc (1 : Fin 2) (by decide) ≫
          (Λ[1, (0 : Fin 1).castSucc].ι ≫
            yonedaEquiv.symm (C.σ 0 x₀)) =
        yonedaEquiv.symm x₀ := by
      have hδσ : C.δ 1 (C.σ 0 x₀) = x₀ :=
        δ_comp_σ_succ_apply (0 : Fin 1) x₀
      rw [← Category.assoc, horn.ι_ι, stdSimplex.δ_comp_yonedaEquiv_symm,
        hδσ]
    rw [eL, eR]
  apply horn.hom_ext
  intro j hj
  rw [← horn.yonedaEquiv_ι, ← yonedaEquiv_comp, ← yonedaEquiv_comp]
  congr 1
  fin_cases j
  · exact absurd rfl hj
  · exact hmaps

end PrismSpecialEdges

/-!
## Source-prescribed prism extension over a cell (§1)

Finite downward induction along `prismSrcFilt`: inner horns are
filled in the quasicategory, the last horn is special by the
vertical-edge identification, and the `n = 0` step is degenerate.
-/

section PrismSrcExtensionCell

variable {n : ℕ} {C : SSet.{u}}

private lemma exists_extension_prismSrcFilt [Quasicategory C]
    (φ₀ : ((prismSrcInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : ∀ hn : 1 ≤ n,
      (Edge.mk' (φ₀.app _ ⟨prismVertZero n,
          prismVertZero_mem_prismSrcInitial hn⟩)).IsEquivalence) :
    ∀ (d m : ℕ), m + d = n + 1 →
      ∃ φm : ((prismSrcFilt n m :
          (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C,
        Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt m) ≫ φm =
          φ₀ := by
  intro d
  induction d with
  | zero =>
    intro m hm
    have hmn1 : m = n + 1 := by omega
    subst hmn1
    refine ⟨(Subcomplex.eqToIso prismSrcFilt_top).hom ≫ φ₀, ?_⟩
    have hid : Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt (n + 1)) ≫
          (Subcomplex.eqToIso prismSrcFilt_top).hom = 𝟙 _ := by
      rw [Subcomplex.eqToIso_hom, ← cancel_mono (prismSrcInitial n).ι]
      simp
    rw [← Category.assoc, hid, Category.id_comp]
  | succ d ih =>
    intro m hm
    have hm1 : (m + 1) + d = n + 1 := by omega
    obtain ⟨φ₁, hφ₁⟩ := ih (m + 1) hm1
    have hmn : m ≤ n := by omega
    have hpre := prismSrcFilt_preimage_prismTauMap.{u} (⟨m, by omega⟩ :
      Fin (n + 1))
    obtain ⟨σC, hσC⟩ : ∃ σC : Δ[n + 1] ⟶ C,
        Subcomplex.hornLift (prismSrcFilt n (m + 1))
            (prismTau n ⟨m, by omega⟩)
            (⟨m, by omega⟩ : Fin (n + 1)).castSucc hpre ≫ φ₁ =
          Λ[n + 1, (⟨m, by omega⟩ : Fin (n + 1)).castSucc].ι ≫ σC := by
      by_cases hm0 : m = 0
      · subst hm0
        by_cases hn0 : n = 0
        · subst hn0
          exact exists_degen_filler_prismSrc_zero φ₁
        · have hn1 : 1 ≤ n := by omega
          obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
          refine exists_fill_horn_left_of_isEquivalence _ ?_
          exact isEquivalence_leftHornEdge_prismSrcStep m' hφ₁
            (hVert hn1)
      · have hk0 : (0 : Fin (n + 2)) <
            (⟨m, by omega⟩ : Fin (n + 1)).castSucc := by
          rw [Fin.lt_def, Fin.val_castSucc]
          change 0 < m
          omega
        have hkn : (⟨m, by omega⟩ : Fin (n + 1)).castSucc <
            Fin.last (n + 1) := by
          rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
          change m < n + 1
          omega
        exact Quasicategory.hornFilling hk0 hkn _
    obtain ⟨φ', hφ'1, -⟩ := Subcomplex.exists_extension_sup_of_horn_filler hpre
      (fun h ↦ injective_of_mono _ h) φ₁ σC hσC
    refine ⟨(Subcomplex.eqToIso (prismSrcFilt_eq_succ_sup hmn)).hom ≫
        φ', ?_⟩
    have hcomp : Subcomplex.homOfLE
          (prismSrcInitial_le_prismSrcFilt m) ≫
          (Subcomplex.eqToIso (prismSrcFilt_eq_succ_sup hmn)).hom =
        Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt (m + 1)) ≫
          Subcomplex.homOfLE (show prismSrcFilt n (m + 1) ≤
            prismSrcFilt n (m + 1) ⊔
              Subcomplex.ofSimplex
                (prismTau n ⟨m, Nat.lt_succ_of_le hmn⟩) from
            le_sup_left) := by
      rw [Subcomplex.eqToIso_hom, ← cancel_mono (Subcomplex.ι _)]
      simp only [Category.assoc, Subcomplex.homOfLE_ι]
    rw [← Category.assoc, hcomp, Category.assoc, hφ'1]
    exact hφ₁

/-- **Source-prescribed `Δ[1]`-prism extension over a cell**
(the supporting results(i), closing the source half of `PrismCobase.lean`
item (i)). A map out of `∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {0}` into a
quasicategory extends to the prism `Δ[n] ⊗ Δ[1]` as soon as the
image of the vertical edge at vertex `0` is an equivalence (no
hypothesis is needed for `n = 0`, where the filler is
degenerate). The proof is the downward induction along
`SSet.prismSrcFilt` of §1 of the header. -/
theorem exists_extension_of_unionProd_boundary_face_zero
    [Quasicategory C]
    (φ₀ : ((prismSrcInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : ∀ hn : 1 ≤ n,
      (Edge.mk' (φ₀.app _ ⟨prismVertZero n,
          prismVertZero_mem_prismSrcInitial hn⟩)).IsEquivalence) :
    ∃ F : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ C,
      (prismSrcInitial n).ι ≫ F = φ₀ := by
  obtain ⟨φm, hφm⟩ := exists_extension_prismSrcFilt φ₀ hVert (n + 1) 0
    (by omega)
  set iso : ((prismSrcFilt n 0 :
      (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≅
      (Δ[n] ⊗ Δ[1] : SSet.{u}) :=
    Subcomplex.eqToIso prismSrcFilt_zero ≪≫ Subcomplex.topIso _ with hiso
  refine ⟨iso.inv ≫ φm, ?_⟩
  have hhom : iso.hom = (prismSrcFilt n 0).ι := by
    rw [hiso, Iso.trans_hom, Subcomplex.eqToIso_hom,
      Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]
  have hι : (prismSrcInitial n).ι =
      Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt 0) ≫
        iso.hom := by
    rw [hhom]
    exact (Subcomplex.homOfLE_ι _).symm
  rw [hι, Category.assoc, ← Category.assoc iso.hom iso.inv φm,
    Iso.hom_inv_id, Category.id_comp]
  exact hφm

end PrismSrcExtensionCell

/-!
## The target-prescribed (mirror) prism filtration (§1)

The increasing filtration `G'ₘ = S₁ ⊔ ⨆_{k < m} ofSimplex τₖ`
attaches `τₖ` along `Λ[n+1, k+1]`. The face lemmas are shared
with the source filtration; the attaching-horn computation is the
mirror of `SSet.prismSrcFilt_preimage_prismTauMap`.
-/

section PrismTgtFiltration

variable {n : ℕ}

/-- The initial subcomplex for the target-prescribed prism:
`∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {1}`. -/
noncomputable abbrev prismTgtInitial (n : ℕ) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
  Subcomplex.unionProd ∂Δ[n] (stdSimplex.face {1})

/-- The increasing prism filtration: `S₁` together with the top
simplices `τₖ` for `k < m`. -/
noncomputable def prismTgtFilt (n : ℕ) (m : ℕ) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
  prismTgtInitial n ⊔ ⨆ (k : Fin (n + 1)) (_ : k.val < m),
    Subcomplex.ofSimplex (prismTau n k)

lemma prismTgtInitial_le_prismTgtFilt (m : ℕ) :
    prismTgtInitial n ≤ prismTgtFilt n m :=
  le_sup_left

lemma ofSimplex_prismTau_le_prismTgtFilt {m : ℕ} {k : Fin (n + 1)}
    (h : k.val < m) :
    Subcomplex.ofSimplex (prismTau n k) ≤ prismTgtFilt n m := by
  unfold prismTgtFilt
  refine (le_iSup_of_le k ?_).trans le_sup_right
  exact le_iSup_of_le h le_rfl

lemma prismTgtFilt_le_succ (m : ℕ) :
    prismTgtFilt n m ≤ prismTgtFilt n (m + 1) := by
  unfold prismTgtFilt
  apply sup_le le_sup_left
  apply iSup_le
  intro k
  apply iSup_le
  intro h
  refine (le_iSup_of_le k ?_).trans le_sup_right
  exact le_iSup_of_le (Nat.lt_trans h (Nat.lt_succ_self m)) le_rfl

/-- One mirror filtration step: `G'ₘ₊₁ = G'ₘ ⊔ ofSimplex τₘ`. -/
lemma prismTgtFilt_succ_eq_sup {m : ℕ} (hm : m ≤ n) :
    prismTgtFilt n (m + 1) = prismTgtFilt n m ⊔
      Subcomplex.ofSimplex (prismTau n ⟨m, by omega⟩) := by
  apply le_antisymm
  · unfold prismTgtFilt
    apply sup_le (le_sup_left.trans le_sup_left)
    apply iSup_le
    intro k
    apply iSup_le
    intro h
    by_cases hk : k.val = m
    · have hke : k = ⟨m, by omega⟩ := Fin.ext hk
      rw [hke]
      exact le_sup_right
    · refine (le_iSup_of_le k ?_).trans
        (le_sup_right.trans le_sup_left)
      exact le_iSup_of_le (show k.val < m by omega) le_rfl
  · exact sup_le (prismTgtFilt_le_succ m)
      (ofSimplex_prismTau_le_prismTgtFilt (Nat.lt_succ_self m))

/-- The bottom of the increasing filtration is the target initial
subcomplex. -/
lemma prismTgtFilt_zero :
    prismTgtFilt n 0 = prismTgtInitial n := by
  refine le_antisymm ?_ le_sup_left
  unfold prismTgtFilt
  refine sup_le le_rfl ?_
  apply iSup_le
  intro k
  apply iSup_le
  intro h
  exfalso
  exact Nat.not_lt_zero _ h

/-- The top of the increasing filtration is the whole prism. -/
lemma prismTgtFilt_top : prismTgtFilt n (n + 1) = ⊤ := by
  refine (prodStdSimplex.subcomplex_eq_top_iff
    (prismTgtFilt n (n + 1)) rfl).2 ?_
  intro x hx
  obtain ⟨k, hk⟩ :=
    prodStdSimplex₁.nonDegenerateEquiv.surjective ⟨x, hx⟩
  have hval : prismTau n k = x := congrArg Subtype.val hk
  rw [← hval]
  exact ofSimplex_prismTau_le_prismTgtFilt k.isLt _
    (Subcomplex.mem_ofSimplex_obj _)

/-- The diagonal simplex `codimOneSimplex j` does not lie in the
target initial subcomplex when its second coordinates take the
value `0`: its first component is the fundamental simplex of
`Δ[n]`. -/
lemma codimOne_notMem_prismTgtInitial {j : Fin (n + 2)}
    {t₀ : Fin (n + 1)}
    (ht₀ : stdSimplex.objMk₁.{u} j t₀ = 0) :
    ((prodStdSimplex₁.codimOneSimplex j).1 :
      (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋n⦌) ∉
      (prismTgtInitial n).obj _ := by
  intro hmem
  have hmem2 := (Subcomplex.mem_unionProd_iff _ _ _).1 hmem
  rcases hmem2 with hsnd | hfst
  · have h1 := (stdSimplex.mem_face_iff _ _).1 hsnd t₀
    rw [codimOne_snd, ht₀] at h1
    simp at h1
  · rw [codimOne_fst] at hfst
    exact stdSimplex.notMem_boundary n hfst

/-- **The attaching horn for the increasing filtration**: the
preimage of `G'ₖ` under `τₖ` is `Λ[n+1, k+1]`. The face omitting
`(k,0)` is shared with `τₖ₋₁` (over the top face for `k = 0`);
the missing diagonal face omitting `(k,1)` is in neither `S₁`
nor any earlier `τ_{k'}`, by the vertex `(k, 0)` of its range. -/
lemma prismTgtFilt_preimage_prismTauMap (k : Fin (n + 1)) :
    (prismTgtFilt n k.val).preimage (prismTauMap.{u} n k) =
      Λ[n + 1, k.succ] := by
  apply le_antisymm
  · rw [subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      image_face_singleton_compl_prismTauMap,
      prodStdSimplex₁.δ_succ_nonDegenerateEquiv,
      Subcomplex.ofSimplex_le_iff]
    intro hmem
    unfold prismTgtFilt at hmem
    rw [Subfunctor.max_obj, Set.mem_union] at hmem
    rcases hmem with h0 | hI
    · exact codimOne_notMem_prismTgtInitial (j := k.succ)
        (t₀ := ⟨k.val, k.isLt⟩) (by
          rw [stdSimplex.objMk₁_apply]
          have hlt : (⟨k.val, k.isLt⟩ : Fin (n + 1)).castSucc <
              k.succ := by
            rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
            exact Nat.lt_succ_self _
          simp only [hlt, ↓reduceIte]) h0
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hI
      obtain ⟨k', hlt, hmem'⟩ := hI
      have hle2 : Set.range (prodStdSimplex.objEquiv.{u}
          (prodStdSimplex₁.codimOneSimplex k.succ).1) ⊆
          Set.range (prodStdSimplex.objEquiv.{u} (prismTau n k')) :=
        (prodStdSimplex.ofSimplex_le_ofSimplex_iff _ _).1
          ((Subcomplex.ofSimplex_le_iff _ _).2 hmem')
      have hmemK : (⟨k.val, k.isLt⟩, (0 : Fin 2)) ∈ Set.range
          (prodStdSimplex.objEquiv.{u}
            (prodStdSimplex₁.codimOneSimplex k.succ).1) :=
        mem_range_codimOne_objEquiv.2
          (Or.inl ⟨rfl, by
            rw [Fin.val_succ]
            exact Nat.lt_succ_self _⟩)
      have hthis := hle2 hmemK
      have hle' : (⟨k.val, k.isLt⟩ : Fin (n + 1)) ≤ k' :=
        (prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₀_iff
          k' ⟨k.val, k.isLt⟩).1 hthis
      change k.val ≤ k'.val at hle'
      omega
  · rw [horn_eq_iSup]
    apply iSup_le
    rintro ⟨j, hj⟩
    have hj' : j ≠ k.succ := by
      simpa using hj
    rw [← Subcomplex.image_le_iff,
      image_face_singleton_compl_prismTauMap]
    by_cases hjk : j.val < k.val
    · exact (prismTau_δ_ofSimplex_le_boundary_prod_top_of_lt
        hjk).trans ((Subcomplex.prod_top_le_unionProd _ _).trans
          (prismTgtInitial_le_prismTgtFilt _))
    · by_cases hjk2 : k.val + 1 < j.val
      · exact (prismTau_δ_ofSimplex_le_boundary_prod_top_of_gt
          hjk2).trans ((Subcomplex.prod_top_le_unionProd _ _).trans
            (prismTgtInitial_le_prismTgtFilt _))
      · have hne : j.val ≠ k.val + 1 := fun hv ↦ hj' (Fin.ext (by
            rw [Fin.val_succ]; exact hv))
        have hj_eq : j = k.castSucc := Fin.ext (by
          show j.val = (k.castSucc).val
          rw [Fin.val_castSucc]
          omega)
        subst hj_eq
        rw [prodStdSimplex₁.δ_castSucc_nonDegenerateEquiv]
        by_cases hk0 : k.val = 0
        · refine (ofSimplex_le_top_prod_of_snd_mem ?_).trans
            ((Subcomplex.top_prod_le_unionProd _ _).trans
              (prismTgtInitial_le_prismTgtFilt _))
          rw [codimOne_snd, stdSimplex.mem_face_iff]
          intro t
          rw [stdSimplex.objMk₁_apply]
          have ht : ¬ t.castSucc < k.castSucc := by
            rw [Fin.lt_def, Fin.val_castSucc, Fin.val_castSucc, hk0]
            exact Nat.not_lt_zero _
          simp only [ht, ↓reduceIte, Finset.mem_singleton]
        · have hkk : (⟨k.val - 1, by omega⟩ : Fin (n + 1)).succ =
              k.castSucc :=
            Fin.ext (by
              change ((⟨k.val - 1, by omega⟩ : Fin (n + 1)).succ).val =
                k.val
              rw [Fin.val_succ]
              change k.val - 1 + 1 = k.val
              omega)
          have hδ :=
            prodStdSimplex₁.δ_succ_nonDegenerateEquiv
              (⟨k.val - 1, by omega⟩ : Fin (n + 1))
          rw [hkk] at hδ
          rw [← hδ]
          have hmem'' : (Δ[n] ⊗ Δ[1] : SSet.{u}).δ k.castSucc
                (prismTau n ⟨k.val - 1, by omega⟩) ∈
              (Subcomplex.ofSimplex
                (prismTau n ⟨k.val - 1, by omega⟩)).obj _ :=
            (Subcomplex.ofSimplex
              (prismTau n ⟨k.val - 1, by omega⟩)).map _
              (Subcomplex.mem_ofSimplex_obj _)
          exact ((Subcomplex.ofSimplex_le_iff _ _).2 hmem'').trans
            (ofSimplex_prismTau_le_prismTgtFilt
              (show (⟨k.val - 1, by omega⟩ : Fin (n + 1)).val <
                k.val from by
                change k.val - 1 < k.val
                omega))

/-- For `n ≥ 1` the vertical edge at vertex `n` lies in the
target initial subcomplex, through its boundary factor. -/
lemma prismVertLast_mem_prismTgtInitial (hn : 1 ≤ n) :
    prismVertLast.{u} n ∈ (prismTgtInitial n).obj _ :=
  (Subcomplex.prod_top_le_unionProd ∂Δ[n] (stdSimplex.face {1})) _
    (prismVertLast_mem_boundary_prod hn)

/-- The vertical edge at vertex `n` lies in every stage of the
target filtration. -/
lemma prismVertLast_mem_prismTgtFilt (hn : 1 ≤ n) (m : ℕ) :
    prismVertLast.{u} n ∈ (prismTgtFilt n m).obj _ :=
  (prismTgtInitial_le_prismTgtFilt m) _
    (prismVertLast_mem_prismTgtInitial hn)

end PrismTgtFiltration

/-!
## The special edge of the last mirror horn and target extension

Mirror of `PrismSpecialEdges`/`PrismSrcExtensionCell`: the last
edge of `Λ[n+1, n+1]` is the vertical at vertex `n`, the `n = 0`
step is degenerate at `(0,1)`, and the induction runs upwards.
-/

section PrismTgtExtensionCell

variable {n : ℕ} {C : SSet.{u}}

/-- The horn lift for `τₙ` sends the last-edge simplex of
`Λ[m+2, m+2]` to the vertical edge at vertex `m+1`. -/
lemma hornLift_app_rightHornEdgeSimplex (m : ℕ) :
    (Subcomplex.hornLift (prismTgtFilt (m + 1) (m + 1))
        (prismTau (m + 1) ⟨m + 1, by omega⟩)
        (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
        (prismTgtFilt_preimage_prismTauMap
          (⟨m + 1, by omega⟩ : Fin (m + 2)))).app _
        (rightHornEdgeSimplex.{u} m) =
      ⟨prismVertLast (m + 1),
        prismVertLast_mem_prismTgtFilt (by omega) (m + 1)⟩ := by
  apply Subtype.ext
  calc ((Subcomplex.hornLift (prismTgtFilt (m + 1) (m + 1))
          (prismTau (m + 1) ⟨m + 1, by omega⟩)
          (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
          (prismTgtFilt_preimage_prismTauMap
            (⟨m + 1, by omega⟩ : Fin (m + 2)))).app _
          (rightHornEdgeSimplex.{u} m)).val
      = (prismTauMap.{u} (m + 1) ⟨m + 1, by omega⟩).app _
          (stdSimplex.edge (m + 2) ⟨m + 1, by omega⟩
            ⟨m + 2, by omega⟩ (by simp [Fin.le_def])) :=
        congr($(Subcomplex.hornLift_ι
          (prismTgtFilt_preimage_prismTauMap
            (⟨m + 1, by omega⟩ : Fin (m + 2)))).app _
            (rightHornEdgeSimplex.{u} m))
    _ = prismVertLast (m + 1) := prismTauMap_last_app_edge

/-- The last edge of the last mirror-filtration horn map is the
image of the vertical edge at the last vertex. -/
lemma rightHornEdge_hornLift_comp (m : ℕ)
    (φ : ((prismTgtFilt (m + 1) (m + 1) :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    (rightHornEdge
        (Subcomplex.hornLift (prismTgtFilt (m + 1) (m + 1))
            (prismTau (m + 1) ⟨m + 1, by omega⟩)
            (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
            (prismTgtFilt_preimage_prismTauMap
              (⟨m + 1, by omega⟩ : Fin (m + 2))) ≫ φ)).edge =
      φ.app _ ⟨prismVertLast (m + 1),
        prismVertLast_mem_prismTgtFilt (by omega) (m + 1)⟩ :=
  congrArg (φ.app _) (hornLift_app_rightHornEdgeSimplex m)

/-- The last mirror-filtration horn is special as soon as the
vertical edge at the last vertex of the initial datum is an
equivalence. -/
lemma isEquivalence_rightHornEdge_prismTgtStep (m : ℕ)
    {φ : ((prismTgtFilt (m + 1) (m + 1) :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    {φ₀ : ((prismTgtInitial (m + 1) :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    (hrestr : Subcomplex.homOfLE
        (prismTgtInitial_le_prismTgtFilt (m + 1)) ≫ φ = φ₀)
    (hVert : (Edge.mk' (φ₀.app _ ⟨prismVertLast (m + 1),
        prismVertLast_mem_prismTgtInitial (by omega)⟩)).IsEquivalence) :
    (rightHornEdge
        (Subcomplex.hornLift (prismTgtFilt (m + 1) (m + 1))
            (prismTau (m + 1) ⟨m + 1, by omega⟩)
            (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
            (prismTgtFilt_preimage_prismTauMap
              (⟨m + 1, by omega⟩ : Fin (m + 2))) ≫ φ)).IsEquivalence := by
  refine (Edge.isEquivalence_iff_of_edge_eq (e :=
      rightHornEdge _) (e' := Edge.mk' (φ₀.app _
        ⟨prismVertLast (m + 1),
          prismVertLast_mem_prismTgtInitial (by omega)⟩)) ?_).2 hVert
  rw [rightHornEdge_hornLift_comp]
  exact congr($(hrestr).app _ ⟨prismVertLast (m + 1),
    prismVertLast_mem_prismTgtInitial (by omega)⟩)

/-- The `δ 0` face of `τ₀` over `Δ[0]` is the vertex `(0,1)`. -/
lemma prismTau_zero_δ_zero :
    (Δ[0] ⊗ Δ[1] : SSet.{u}).δ 0 (prismTau 0 0) =
      prismVertConst 0 (0, 1) := by
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [prism_objEquiv_δ_apply, prismVertConst_objEquiv_apply]
  fin_cases t
  apply Prod.ext
  · apply Fin.ext
    have h := prismTau_objEquiv_fst_val.{u} (n := 0)
      (k := (0 : Fin 1)) (t := (0 : Fin 2).succAbove ⟨0, by omega⟩)
    have hpos : ((0 : Fin 2).succAbove ⟨0, by omega⟩).val = 1 := rfl
    rw [hpos] at h
    change ((prodStdSimplex.objEquiv.{u} (prismTau 0 0)
      ((0 : Fin 2).succAbove ⟨0, by omega⟩)).1).val = 0
    rw [h]
    simp
  · have h := prismTau_objEquiv_snd.{u} (n := 0)
      (k := (0 : Fin 1)) (t := (0 : Fin 2).succAbove ⟨0, by omega⟩)
    have hpos : ((0 : Fin 2).succAbove ⟨0, by omega⟩).val = 1 := rfl
    rw [hpos] at h
    rw [h]
    simp

/-- The constant vertex `(0,1)` lies in the target initial
subcomplex over `Δ[0]`: its second coordinate is `1`. -/
lemma prismVertConst_zero_one_mem_prismTgtInitial :
    prismVertConst.{u} 0 (0, 1) ∈ (prismTgtInitial 0).obj _ := by
  refine (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl ?_)
  rw [stdSimplex.mem_face_iff]
  intro i
  exact Finset.mem_singleton.2 rfl

/-- **The degenerate filler for the `n = 0` target step**: over
`Δ[0]`, the horn `Λ[1, 1]` induced by any map out of
`prismTgtFilt 0 0` is filled by the degenerate edge at the image
of the vertex `(0,1)`. -/
lemma exists_degen_filler_prismTgt_zero
    (φ : ((prismTgtFilt 0 0 :
        (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    ∃ σC : Δ[1] ⟶ C,
      Subcomplex.hornLift (prismTgtFilt 0 0) (prismTau 0 0)
          (0 : Fin 1).succ
          (prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ =
        Λ[1, (0 : Fin 1).succ].ι ≫ σC := by
  set memF : prismVertConst.{u} 0 (0, 1) ∈ (prismTgtFilt 0 0).obj _ :=
    (prismTgtInitial_le_prismTgtFilt 0) _
      prismVertConst_zero_one_mem_prismTgtInitial with hmemF
  set pt : ((prismTgtFilt 0 0 :
      (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) _⦋0⦌ :=
    ⟨prismVertConst 0 (0, 1), memF⟩ with hpt
  set x₁ : C _⦋0⦌ := φ.app _ pt with hx₁
  refine ⟨yonedaEquiv.symm (C.σ 0 x₁), ?_⟩
  have hι : horn.ι (0 : Fin 1).succ (0 : Fin 2) (by decide) ≫
        Subcomplex.hornLift (prismTgtFilt 0 0) (prismTau 0 0)
          (0 : Fin 1).succ
          (prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) =
      yonedaEquiv.symm pt := by
    rw [← cancel_mono (prismTgtFilt 0 0).ι]
    have e1 : horn.ι (0 : Fin 1).succ (0 : Fin 2) (by decide) ≫
          Subcomplex.hornLift (prismTgtFilt 0 0) (prismTau 0 0)
            (0 : Fin 1).succ
            (prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) ≫
          (prismTgtFilt 0 0).ι =
        yonedaEquiv.symm ((Δ[0] ⊗ Δ[1] : SSet.{u}).δ 0 (prismTau 0 0)) := by
      -- As in the source case, `Subcomplex.hornLift_ι` with its
      -- type ascribed in the goal's form (`prismTauMap` is now
      -- the semireducible def `prodStdSimplex₁.ι`).
      have hhl : Subcomplex.hornLift (prismTgtFilt 0 0)
            (prismTau 0 0) (0 : Fin 1).succ
            (prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) ≫
          (prismTgtFilt 0 0).ι =
        Λ[1, (0 : Fin 1).succ].ι ≫
          yonedaEquiv.symm (prismTau 0 0) :=
        Subcomplex.hornLift_ι
          (prismTgtFilt_preimage_prismTauMap (0 : Fin 1))
      rw [hhl, ← Category.assoc, horn.ι_ι,
        stdSimplex.δ_comp_yonedaEquiv_symm]
    have e2 : yonedaEquiv.symm pt ≫
          (prismTgtFilt 0 0).ι =
        yonedaEquiv.symm (prismVertConst 0 (0, 1)) := by
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
      rfl
    rw [Category.assoc, e1, e2, prismTau_zero_δ_zero]
  have hmaps : horn.ι (0 : Fin 1).succ (0 : Fin 2) (by decide) ≫
        (Subcomplex.hornLift (prismTgtFilt 0 0) (prismTau 0 0)
            (0 : Fin 1).succ
            (prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ) =
      horn.ι (0 : Fin 1).succ (0 : Fin 2) (by decide) ≫
        (Λ[1, (0 : Fin 1).succ].ι ≫
          yonedaEquiv.symm (C.σ 0 x₁)) := by
    have eL : horn.ι (0 : Fin 1).succ (0 : Fin 2) (by decide) ≫
          (Subcomplex.hornLift (prismTgtFilt 0 0) (prismTau 0 0)
              (0 : Fin 1).succ
              (prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ) =
        yonedaEquiv.symm x₁ := by
      rw [← Category.assoc, hι]
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact hx₁.symm
    have eR : horn.ι (0 : Fin 1).succ (0 : Fin 2) (by decide) ≫
          (Λ[1, (0 : Fin 1).succ].ι ≫
            yonedaEquiv.symm (C.σ 0 x₁)) =
        yonedaEquiv.symm x₁ := by
      have hδσ : C.δ 0 (C.σ 0 x₁) = x₁ :=
        δ_comp_σ_self_apply (0 : Fin 1) x₁
      rw [← Category.assoc, horn.ι_ι, stdSimplex.δ_comp_yonedaEquiv_symm,
        hδσ]
    rw [eL, eR]
  apply horn.hom_ext
  intro j hj
  rw [← horn.yonedaEquiv_ι, ← yonedaEquiv_comp, ← yonedaEquiv_comp]
  congr 1
  fin_cases j
  · exact hmaps
  · exact absurd rfl hj

private lemma exists_extension_prismTgtFilt [Quasicategory C]
    (φ₀ : ((prismTgtInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : ∀ hn : 1 ≤ n,
      (Edge.mk' (φ₀.app _ ⟨prismVertLast n,
          prismVertLast_mem_prismTgtInitial hn⟩)).IsEquivalence) :
    ∀ (m : ℕ), m ≤ n + 1 →
      ∃ φm : ((prismTgtFilt n m :
          (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C,
        Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt m) ≫ φm =
          φ₀ := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨(Subcomplex.eqToIso prismTgtFilt_zero).hom ≫ φ₀, ?_⟩
    have hid : Subcomplex.homOfLE
          (prismTgtInitial_le_prismTgtFilt (n := n) 0) ≫
          (Subcomplex.eqToIso (prismTgtFilt_zero (n := n))).hom =
          𝟙 _ := by
      rw [Subcomplex.eqToIso_hom, ← cancel_mono (prismTgtInitial n).ι]
      simp
    rw [← Category.assoc, hid, Category.id_comp]
  | succ m ih =>
    intro hm
    obtain ⟨φ₁, hφ₁⟩ := ih (by omega)
    have hmn : m ≤ n := by omega
    have hpre := prismTgtFilt_preimage_prismTauMap.{u}
      (⟨m, by omega⟩ : Fin (n + 1))
    obtain ⟨σC, hσC⟩ : ∃ σC : Δ[n + 1] ⟶ C,
        Subcomplex.hornLift (prismTgtFilt n m)
            (prismTau n ⟨m, by omega⟩)
            (⟨m, by omega⟩ : Fin (n + 1)).succ hpre ≫ φ₁ =
          Λ[n + 1, (⟨m, by omega⟩ : Fin (n + 1)).succ].ι ≫ σC := by
      by_cases hmn' : m = n
      · obtain rfl : n = m := hmn'.symm
        by_cases hn0 : n = 0
        · subst hn0
          exact exists_degen_filler_prismTgt_zero φ₁
        · have hn1 : 1 ≤ n := by omega
          obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
          refine exists_fill_horn_right_of_isEquivalence _ ?_
          exact isEquivalence_rightHornEdge_prismTgtStep m' hφ₁
            (hVert hn1)
      · have hk0 : (0 : Fin (n + 2)) <
            (⟨m, by omega⟩ : Fin (n + 1)).succ := by
          rw [Fin.lt_def, Fin.val_succ]
          change 0 < m + 1
          omega
        have hkn : (⟨m, by omega⟩ : Fin (n + 1)).succ <
            Fin.last (n + 1) := by
          rw [Fin.lt_def, Fin.val_succ, Fin.val_last]
          change m + 1 < n + 1
          omega
        exact Quasicategory.hornFilling hk0 hkn _
    obtain ⟨φ', hφ'1, -⟩ := Subcomplex.exists_extension_sup_of_horn_filler hpre
      (fun h ↦ injective_of_mono _ h) φ₁ σC hσC
    refine ⟨(Subcomplex.eqToIso (prismTgtFilt_succ_eq_sup hmn)).hom ≫
        φ', ?_⟩
    have hcomp : Subcomplex.homOfLE
          (prismTgtInitial_le_prismTgtFilt (m + 1)) ≫
          (Subcomplex.eqToIso (prismTgtFilt_succ_eq_sup hmn)).hom =
        Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt m) ≫
          Subcomplex.homOfLE (show prismTgtFilt n m ≤
            prismTgtFilt n m ⊔
              Subcomplex.ofSimplex
                (prismTau n ⟨m, Nat.lt_succ_of_le hmn⟩) from
            le_sup_left) := by
      rw [Subcomplex.eqToIso_hom, ← cancel_mono (Subcomplex.ι _)]
      simp only [Category.assoc, Subcomplex.homOfLE_ι]
    rw [← Category.assoc, hcomp, Category.assoc, hφ'1]
    exact hφ₁

/-- **Target-prescribed `Δ[1]`-prism extension over a cell**
(the supporting results(ii), closing the mirror half of `PrismCobase.lean`
item (ii)). A map out of `∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {1}` into a
quasicategory extends to the prism `Δ[n] ⊗ Δ[1]` as soon as the
image of the vertical edge at the last vertex is an equivalence
(no hypothesis for `n = 0`). -/
theorem exists_extension_of_unionProd_boundary_face_one
    [Quasicategory C]
    (φ₀ : ((prismTgtInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : ∀ hn : 1 ≤ n,
      (Edge.mk' (φ₀.app _ ⟨prismVertLast n,
          prismVertLast_mem_prismTgtInitial hn⟩)).IsEquivalence) :
    ∃ F : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ C,
      (prismTgtInitial n).ι ≫ F = φ₀ := by
  obtain ⟨φm, hφm⟩ := exists_extension_prismTgtFilt φ₀ hVert (n + 1)
    (by omega)
  set iso : ((prismTgtFilt n (n + 1) :
      (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≅
      (Δ[n] ⊗ Δ[1] : SSet.{u}) :=
    Subcomplex.eqToIso prismTgtFilt_top ≪≫ Subcomplex.topIso _ with hiso
  refine ⟨iso.inv ≫ φm, ?_⟩
  have hhom : iso.hom = (prismTgtFilt n (n + 1)).ι := by
    rw [hiso, Iso.trans_hom, Subcomplex.eqToIso_hom,
      Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]
  have hι : (prismTgtInitial n).ι =
      Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt (n + 1)) ≫
        iso.hom := by
    rw [hhom]
    exact (Subcomplex.homOfLE_ι _).symm
  rw [hι, Category.assoc, ← Category.assoc iso.hom iso.inv φm,
    Iso.hom_inv_id, Category.id_comp]
  exact hφm

end PrismTgtExtensionCell

/-!
## From `Δ[2]`-prisms to equivalence of the prism edge (§2)

The formal last step of the pointwise criterion: a `Δ[1]`-prism
edge equipped with an inverse prism and two `Δ[2]`-prisms
witnessing the two compositions with the degenerate prisms is an
equivalence, through `Edge.InvStruct`. The `Δ[2]`-prisms
themselves are exactly the output of the shuffle filtration of
§2 of the header, which remains to be formalized.
-/

section CompPrismsEquivalence

variable {B C : SSet.{u}} {x₀ x₁ : ((ihom B).obj C) _⦋0⦌}

/-- **A prism edge with inverse `Δ[2]`-prisms is an
equivalence.** Given prisms `F G : B ⊗ Δ[1] ⟶ C` between
prescribed vertices and prisms `P Q : B ⊗ Δ[2] ⟶ C` whose
`δ₂`- and `δ₀`-faces are `F, G` (resp. `G, F`) and whose
`δ₁`-face is the degenerate prism at the source vertex, the edge
of `F` in `Fun(B, C)` is an equivalence: the two `Δ[2]`-prisms
are `CompStruct` witnesses through
`SSet.δ_ihomSimplexOfPrism`/`SSet.σ_ihomSimplexOfPrism`, i.e. an
`Edge.InvStruct` for `edgeOfPrism F`. -/
theorem edgeOfPrism_isEquivalence_of_compPrisms
    (F G : B ⊗ Δ[1] ⟶ C)
    (hF₀ : ((ihom B).obj C).δ 1 (ihomSimplexOfPrism F) = x₀)
    (hF₁ : ((ihom B).obj C).δ 0 (ihomSimplexOfPrism F) = x₁)
    (hG₀ : ((ihom B).obj C).δ 1 (ihomSimplexOfPrism G) = x₁)
    (hG₁ : ((ihom B).obj C).δ 0 (ihomSimplexOfPrism G) = x₀)
    (P Q : B ⊗ Δ[2] ⟶ C)
    (hP₂ : (B ◁ stdSimplex.δ 2) ≫ P = F)
    (hP₀ : (B ◁ stdSimplex.δ 0) ≫ P = G)
    (hP₁ : (B ◁ stdSimplex.δ 1) ≫ P =
      (B ◁ stdSimplex.σ 0) ≫ (B ◁ stdSimplex.δ 1) ≫ F)
    (hQ₂ : (B ◁ stdSimplex.δ 2) ≫ Q = G)
    (hQ₀ : (B ◁ stdSimplex.δ 0) ≫ Q = F)
    (hQ₁ : (B ◁ stdSimplex.δ 1) ≫ Q =
      (B ◁ stdSimplex.σ 0) ≫ (B ◁ stdSimplex.δ 1) ≫ G) :
    (edgeOfPrism F hF₀ hF₁).IsEquivalence := by
  have hcompP : Edge.CompStruct (edgeOfPrism F hF₀ hF₁)
      (edgeOfPrism G hG₀ hG₁) (Edge.id x₀) :=
    Edge.CompStruct.mk (ihomSimplexOfPrism P)
      (by rw [δ_ihomSimplexOfPrism, hP₂, edgeOfPrism_edge])
      (by rw [δ_ihomSimplexOfPrism, hP₀, edgeOfPrism_edge])
      (by
        rw [δ_ihomSimplexOfPrism, hP₁, ← σ_ihomSimplexOfPrism,
          ← δ_ihomSimplexOfPrism, hF₀, Edge.id_edge])
  have hcompQ : Edge.CompStruct (edgeOfPrism G hG₀ hG₁)
      (edgeOfPrism F hF₀ hF₁) (Edge.id x₁) :=
    Edge.CompStruct.mk (ihomSimplexOfPrism Q)
      (by rw [δ_ihomSimplexOfPrism, hQ₂, edgeOfPrism_edge])
      (by rw [δ_ihomSimplexOfPrism, hQ₀, edgeOfPrism_edge])
      (by
        rw [δ_ihomSimplexOfPrism, hQ₁, ← σ_ihomSimplexOfPrism,
          ← δ_ihomSimplexOfPrism, hG₀, Edge.id_edge])
  have hI : Edge.InvStruct (edgeOfPrism F hF₀ hF₁) :=
    { inv := edgeOfPrism G hG₀ hG₁, homInvId := hcompP,
      invHomId := hcompQ }
  exact hI.isEquivalence

end CompPrismsEquivalence

/-!
## Faithfulness from `2`-simplex correction (§4, the additional comparison obligation)

The `Δ[2]`-analogue of the supporting results edge correction: a
`CompStruct` `2`-simplex can be corrected rel boundary through
`p` so that its strict image is a prescribed `2`-simplex with the
same boundary edges downstairs. Faithfulness of precomposition
with a cobase change follows by gluing at `Δ[2]` along the
pullback `SSet.isPullback_pre_app_of_isPushout`, exactly as
fullness (the supporting results) follows from edge correction by gluing at
`Δ[1]`.
-/

section FaithfulnessAssembly

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y}
  {j : X ⟶ Y}

private lemma cobaseUncond_edge_map_map {E F G : SSet.{u}}
    {x₀ x₁ : E _⦋0⦌} (e : Edge x₀ x₁) (g : E ⟶ F) (h : F ⟶ G) :
    (e.map g).map h = e.map (g ≫ h) :=
  Edge.ext (by simp [Edge.map_edge])

private lemma cobaseUncond_toHoHom_ofEq {W : SSet.{u}}
    {a b a' b' : W _⦋0⦌} (e : Edge a b) (h₀ : a = a') (h₁ : b = b') :
    (e.ofEq h₀ h₁).toHoHom =
      eqToHom (congrArg HomotopyCategory.mk h₀.symm) ≫ e.toHoHom ≫
        eqToHom (congrArg HomotopyCategory.mk h₁) := by
  subst h₀
  subst h₁
  have hEq : e.ofEq rfl rfl = e := Edge.ext rfl
  rw [hEq]
  change e.toHoHom = eqToHom (rfl : HomotopyCategory.mk a =
    HomotopyCategory.mk a) ≫ e.toHoHom ≫
      eqToHom (rfl : HomotopyCategory.mk b = HomotopyCategory.mk b)
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- **Correction of `2`-simplices rel boundary** through
`p : E ⟶ B`: every `CompStruct` `2`-simplex `s` of `E` can be
replaced by a `2`-simplex `s'` with the same three boundary edges
whose strict image under `p` is a prescribed `CompStruct`
`2`-simplex `t` downstairs with boundary the images of the same
edges. For `p = (pre i).app C` this is the prism extension problem
for homotopies of `Δ[2]`-prisms of §4 of the header; it is the
`Δ[2]`-analogue of
`SSet.exists_edge_correction_of_innerFibration` (the supporting results).
Unlike that `Δ[1]` case, this `Δ[2]` property is false in
general: relative `π₂` classes obstruct correcting to an
arbitrary prescribed `t` (see the correction in the module
header). It is kept, with the theorems conditional on it, as
a formal reduction recording the input shape a corrected
relative-compatibility version would need. -/
def CompCorrection {E B : SSet.{u}} (p : E ⟶ B) : Prop :=
  ∀ {x₀ x₁ x₂ : E _⦋0⦌} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
    {e₀₂ : Edge x₀ x₂}
    (_s : Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (t : Edge.CompStruct (e₀₁.map p) (e₁₂.map p) (e₀₂.map p)),
    ∃ s' : Edge.CompStruct e₀₁ e₁₂ e₀₂, p.app _ s'.simplex = t.simplex

/-- Conjugation of the two restrictions of an edge of `Fun(Y, C)`
to `Fun(A, C)` by the vertex equalities of the pullback square:
the `B`-restriction followed by `pre i` is the `eqToHom`
conjugate of the `X`-restriction followed by `pre f`. -/
private lemma cobaseUncond_pre_toHoHom_conj (C : SSet.{u})
    {y₁ y₂ : ((ihom Y).obj C) _⦋0⦌}
    (hv : ∀ y : ((ihom Y).obj C) _⦋0⦌,
      ((pre f).app C).app _ (((pre j).app C).app _ y) =
        ((pre i).app C).app _ (((pre f').app C).app _ y))
    (eY : Edge y₁ y₂)
    (hedge : ((eY.map ((pre j).app C)).map ((pre f).app C)).edge =
      ((eY.map ((pre f').app C)).map ((pre i).app C)).edge) :
    ((eY.map ((pre f').app C)).map ((pre i).app C)).toHoHom =
      eqToHom (congrArg HomotopyCategory.mk (hv y₁).symm) ≫
        ((eY.map ((pre j).app C)).map ((pre f).app C)).toHoHom ≫
        eqToHom (congrArg HomotopyCategory.mk (hv y₂)) := by
  have hw : ((eY.map ((pre j).app C)).map ((pre f).app C)).ofEq
        (hv y₁) (hv y₂) =
      (eY.map ((pre f').app C)).map ((pre i).app C) :=
    Edge.ext hedge
  rw [← cobaseUncond_toHoHom_ofEq
    ((eY.map ((pre j).app C)).map ((pre f).app C)) (hv y₁) (hv y₂)]
  exact congrArg Edge.toHoHom hw.symm

/-- Faces of a glued `2`-simplex of `Fun(Y, C)` are read off from
either projection, by joint monicity of the pullback square
`SSet.isPullback_pre_app_of_isPushout`. -/
private lemma cobaseUncond_δ_yonedaEquiv_of_lift
    (sq : IsPushout i f f' j) (C : SSet.{u})
    {Wmap : Δ[2] ⟶ (ihom Y).obj C}
    {sBe : ((ihom B).obj C) _⦋2⦌} {sXe : ((ihom X).obj C) _⦋2⦌}
    {sY : ((ihom Y).obj C) _⦋1⦌} {idx : Fin 3}
    (hB : Wmap ≫ (pre f').app C = yonedaEquiv.symm sBe)
    (hX : Wmap ≫ (pre j).app C = yonedaEquiv.symm sXe)
    (hBy : ((ihom B).obj C).δ idx sBe = ((pre f').app C).app _ sY)
    (hXy : ((ihom X).obj C).δ idx sXe = ((pre j).app C).app _ sY) :
    ((ihom Y).obj C).δ idx (yonedaEquiv Wmap) = sY := by
  have hks : yonedaEquiv.symm (((ihom Y).obj C).δ idx
        (yonedaEquiv Wmap)) =
      yonedaEquiv.symm sY := by
    apply (isPullback_pre_app_of_isPushout sq C).hom_ext
    · apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp]
      simp only [Equiv.apply_symm_apply]
      calc ((pre f').app C).app _
            (((ihom Y).obj C).δ idx (yonedaEquiv Wmap))
          = ((ihom B).obj C).δ idx
              (((pre f').app C).app _ (yonedaEquiv Wmap)) :=
            δ_naturality_apply ((pre f').app C) idx (yonedaEquiv Wmap)
        _ = ((ihom B).obj C).δ idx sBe := by
            rw [← yonedaEquiv_comp, hB, Equiv.apply_symm_apply]
        _ = ((pre f').app C).app _ sY := hBy
    · apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp]
      simp only [Equiv.apply_symm_apply]
      calc ((pre j).app C).app _
            (((ihom Y).obj C).δ idx (yonedaEquiv Wmap))
          = ((ihom X).obj C).δ idx
              (((pre j).app C).app _ (yonedaEquiv Wmap)) :=
            δ_naturality_apply ((pre j).app C) idx (yonedaEquiv Wmap)
        _ = ((ihom X).obj C).δ idx sXe := by
            rw [← yonedaEquiv_comp, hX, Equiv.apply_symm_apply]
        _ = ((pre j).app C).app _ sY := hXy
  have h2 := congrArg yonedaEquiv hks
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2

/-- **Faithfulness of precomposition with a cobase change,
granted `2`-simplex correction.** In a pushout square with
`f` a categorical equivalence (no hypothesis on `i` is used), if
`2`-simplices correct through `(pre i).app C` rel boundary
(`SSet.CompCorrection`), then precomposition with `f'` is
faithful on homotopy categories into `C`: represent the two
morphisms by edges, witness their downstairs equality in
`Fun(B, C)` and (through the equivalence `hFun(f, C)`) in
`Fun(X, C)` by `CompStruct` `2`-simplices, correct the first so
the two agree strictly in `Fun(A, C)`, and glue at `Δ[2]`. -/
theorem hoFunctor_pre_faithful_of_isPushout_of_compCorrection
    (sq : IsPushout i f f' j) (hf : categoricalEquivalences f)
    (C : SSet.{u}) [Quasicategory C]
    (hCorr : CompCorrection ((pre i).app C)) :
    (hoFunctor.map ((pre f').app C)).toFunctor.Faithful := by
  have hFf : (hoFunctor.map ((pre f).app C)).toFunctor.IsEquivalence :=
    (categoricalEquivalences.mem_iff f).1 hf C inferInstance
  have hFf' : (mapHomotopyCategory ((pre f).app C)).IsEquivalence := hFf
  have := hFf'
  change (mapHomotopyCategory ((pre f').app C)).Faithful
  constructor
  intro P Q φ ψ hφψ
  obtain ⟨y₁, rfl⟩ : ∃ y, HomotopyCategory.mk y = P :=
    ⟨_, HomotopyCategory.objEquiv.left_inv P⟩
  obtain ⟨y₂, rfl⟩ : ∃ y, HomotopyCategory.mk y = Q :=
    ⟨_, HomotopyCategory.objEquiv.left_inv Q⟩
  obtain ⟨eYφ, hφ⟩ := Edge.exists_toHoHom_eq φ
  obtain ⟨eYψ, hψ⟩ := Edge.exists_toHoHom_eq ψ
  have hv : ∀ y : ((ihom Y).obj C) _⦋0⦌,
      ((pre f).app C).app _ (((pre j).app C).app _ y) =
        ((pre i).app C).app _ (((pre f').app C).app _ y) := by
    intro y
    have key1 : (pre j).app C ≫ (pre f).app C = (pre (f ≫ j)).app C := by
      rw [pre_map]; rfl
    have key2 : (pre f').app C ≫ (pre i).app C = (pre (i ≫ f')).app C := by
      rw [pre_map]; rfl
    change (((pre j).app C ≫ (pre f).app C).app _ y) =
      (((pre f').app C ≫ (pre i).app C).app _ y)
    rw [key1, key2, sq.w]
  have huB : (eYφ.map ((pre f').app C)).toHoHom =
      (eYψ.map ((pre f').app C)).toHoHom := by
    rw [Edge.toHoHom_map, Edge.toHoHom_map, hφ, hψ]
    exact hφψ
  have hedgeA : ∀ eY : Edge y₁ y₂,
      ((eY.map ((pre j).app C)).map ((pre f).app C)).edge =
        ((eY.map ((pre f').app C)).map ((pre i).app C)).edge := by
    intro eY
    rw [cobaseUncond_edge_map_map, cobaseUncond_edge_map_map,
      Edge.map_edge, Edge.map_edge]
    have key1 : (pre j).app C ≫ (pre f).app C = (pre (f ≫ j)).app C := by
      rw [pre_map]; rfl
    have key2 : (pre f').app C ≫ (pre i).app C = (pre (i ≫ f')).app C := by
      rw [pre_map]; rfl
    rw [key1, key2, sq.w]
  have huB' : ((eYφ.map ((pre f').app C)).map
        ((pre i).app C)).toHoHom =
      ((eYψ.map ((pre f').app C)).map ((pre i).app C)).toHoHom := by
    rw [Edge.toHoHom_map (eYφ.map ((pre f').app C)) ((pre i).app C),
      Edge.toHoHom_map (eYψ.map ((pre f').app C)) ((pre i).app C), huB]
  have huX : (eYφ.map ((pre j).app C)).toHoHom =
      (eYψ.map ((pre j).app C)).toHoHom := by
    apply (mapHomotopyCategory ((pre f).app C)).map_injective
    rw [← Edge.toHoHom_map (eYφ.map ((pre j).app C)) ((pre f).app C),
      ← Edge.toHoHom_map (eYψ.map ((pre j).app C)) ((pre f).app C)]
    have step : ∀ eY : Edge y₁ y₂,
        ((eY.map ((pre j).app C)).map ((pre f).app C)).toHoHom =
          eqToHom (congrArg HomotopyCategory.mk (hv y₁)) ≫
            ((eY.map ((pre f').app C)).map ((pre i).app C)).toHoHom ≫
            eqToHom (congrArg HomotopyCategory.mk (hv y₂).symm) := by
      intro eY
      have h1 := cobaseUncond_pre_toHoHom_conj C hv eY (hedgeA eY)
      rw [h1]
      simp
    rw [step, step, huB']
  obtain ⟨sB⟩ := Edge.nonempty_compStruct_of_toHoHom_comp_eq
    (show (eYφ.map ((pre f').app C)).toHoHom ≫
        (Edge.id _).toHoHom =
      (eYψ.map ((pre f').app C)).toHoHom by
      rw [Edge.toHoHom_id, Category.comp_id]; exact huB)
  obtain ⟨sX⟩ := Edge.nonempty_compStruct_of_toHoHom_comp_eq
    (show (eYφ.map ((pre j).app C)).toHoHom ≫
        (Edge.id _).toHoHom =
      (eYψ.map ((pre j).app C)).toHoHom by
      rw [Edge.toHoHom_id, Category.comp_id]; exact huX)
  have hid : ((Edge.id (((pre j).app C).app _ y₂)).map
        ((pre f).app C)).edge =
      ((Edge.id (((pre f').app C).app _ y₂)).map ((pre i).app C)).edge := by
    calc ((Edge.id (((pre j).app C).app _ y₂)).map
          ((pre f).app C)).edge
        = (Edge.id (((pre f).app C).app _
            (((pre j).app C).app _ y₂))).edge :=
          congrArg Edge.edge (Edge.map_id _ _)
      _ = ((ihom A).obj C).σ 0 (((pre f).app C).app _
            (((pre j).app C).app _ y₂)) := Edge.id_edge _
      _ = ((ihom A).obj C).σ 0 (((pre i).app C).app _
            (((pre f').app C).app _ y₂)) :=
          congrArg _ (hv y₂)
      _ = (Edge.id (((pre i).app C).app _
            (((pre f').app C).app _ y₂))).edge := (Edge.id_edge _).symm
      _ = ((Edge.id (((pre f').app C).app _ y₂)).map
            ((pre i).app C)).edge :=
          congrArg Edge.edge (Edge.map_id _ _).symm
  set t : Edge.CompStruct
      ((eYφ.map ((pre f').app C)).map ((pre i).app C))
      ((Edge.id (((pre f').app C).app _ y₂)).map ((pre i).app C))
      ((eYψ.map ((pre f').app C)).map ((pre i).app C)) :=
    (sX.map ((pre f).app C)).ofEq (hedgeA eYφ) hid (hedgeA eYψ) with htdef
  have ht : t.simplex = ((pre f).app C).app _ sX.simplex := rfl
  obtain ⟨sB', hsB'⟩ := hCorr sB t
  have hagree : yonedaEquiv.symm sB'.simplex ≫ (pre i).app C =
      yonedaEquiv.symm sX.simplex ≫ (pre f).app C := by
    apply yonedaEquiv.injective
    simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    rw [hsB', ht]
  obtain ⟨Wmap, hW1, hW2⟩ := exists_pre_lift_of_isPushout sq C _ _ hagree
  have hface2 : ((ihom Y).obj C).δ 2 (yonedaEquiv Wmap) = eYφ.edge :=
    cobaseUncond_δ_yonedaEquiv_of_lift sq C hW1 hW2
      (by rw [sB'.d₂, Edge.map_edge]) (by rw [sX.d₂, Edge.map_edge])
  have hface0 : ((ihom Y).obj C).δ 0 (yonedaEquiv Wmap) =
      (Edge.id y₂).edge :=
    cobaseUncond_δ_yonedaEquiv_of_lift sq C hW1 hW2
      (by rw [sB'.d₀, ← Edge.map_edge, Edge.map_id])
      (by rw [sX.d₀, ← Edge.map_edge, Edge.map_id])
  have hface1 : ((ihom Y).obj C).δ 1 (yonedaEquiv Wmap) = eYψ.edge :=
    cobaseUncond_δ_yonedaEquiv_of_lift sq C hW1 hW2
      (by rw [sB'.d₁, Edge.map_edge]) (by rw [sX.d₁, Edge.map_edge])
  have hCS : Edge.CompStruct eYφ (Edge.id y₂) eYψ :=
    Edge.CompStruct.mk (yonedaEquiv Wmap) hface2 hface0 hface1
  rw [← hφ, ← hψ]
  have hc := Edge.toHoHom_comp hCS
  rwa [Edge.toHoHom_id, Category.comp_id] at hc

/-- **Cobase change of a categorical equivalence along a
monomorphism, granted (A) and `2`-simplex correction.** the supporting results assembly
`SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_faithful`
with the isofibration input supplied by prism strict extension
(the supporting result) and faithfulness by
`SSet.hoFunctor_pre_faithful_of_isPushout_of_compCorrection`. -/
theorem categoricalEquivalences.of_isPushout_of_prismStrictExtension_of_compCorrection
    (sq : IsPushout i f f' j) [Mono i] (hf : categoricalEquivalences f)
    (hA : ∀ (C : SSet.{u}) [Quasicategory C],
      HoPrePrismStrictExtension i C)
    (hCorr : ∀ (C : SSet.{u}) [Quasicategory C],
      CompCorrection ((pre i).app C)) :
    categoricalEquivalences f' :=
  categoricalEquivalences.of_isPushout_of_isIsofibration_of_faithful
    sq hf
    (fun C _ ↦ hoFunctor_pre_isIsofibration_of_prismStrictExtension C
      (hA C))
    (fun C _ ↦ hoFunctor_pre_faithful_of_isPushout_of_compCorrection
      sq hf C (hCorr C))

/-- **Stability of categorical equivalences under cobase change
against monomorphisms, granted prism strict extension (A) and
`2`-simplex correction (B2) for every monomorphism.** This is the
target instance
`(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
(MorphismProperty.monomorphisms SSet)` with exactly the two
remaining prism inputs as hypotheses; see the TODO list at the
end of this module. -/
theorem
    categoricalEquivalences_isStableUnderCobaseChangeAgainst_mono_of_prism_of_correction
    (hA : ∀ {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (C : SSet.{u})
      [Quasicategory C], HoPrePrismStrictExtension i C)
    (hCorr : ∀ {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (C : SSet.{u})
      [Quasicategory C], CompCorrection ((pre i).app C)) :
    categoricalEquivalences.IsStableUnderCobaseChangeAgainst
      (MorphismProperty.monomorphisms SSet.{u}) := by
  constructor
  intro A B i hi
  have : Mono i := hi
  constructor
  intro Z W f' g' g sq hf
  exact
    categoricalEquivalences.of_isPushout_of_prismStrictExtension_of_compCorrection
      sq hf (hA i) (hCorr i)

end FaithfulnessAssembly

end SSet

end
