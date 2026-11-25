/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Homotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidAction
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import MathlibExt.AlgebraicTopology.SimplicialSet.ProdStdSimplexOneCompat

/-!
# Homotopy invariance of Kan weak equivalences

Homotopy inverses induce `KanComplex.W`. The prism
`(RelativeMorphism.map s ▷ Δ[1]) ≫ H.h` gives the
`ActionStruct` witness; the action transports `π.map`.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace SSet

namespace KanComplex

namespace FundamentalGroupoid

variable {X Y : SSet.{u}} [KanComplex Y] {f g : X ⟶ Y}
  (H : Homotopy f g)
variable {n : ℕ} {x : X _⦋0⦌} (s : X.PtSimplex n x)

private lemma ι_zero_snd :
    (prodStdSimplex₁.ι (0 : Fin 1) : Δ[1] ⟶ Δ[0] ⊗ Δ[1]) ≫
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) = 𝟙 _ := by
  apply SSet.yonedaEquiv.injective
  ext i
  fin_cases i <;> rfl

private lemma const_cylinder (x : X _⦋0⦌) :
    (SSet.const (X := (SSet.boundary n : SSet.{u})) x ▷
      (Δ[1] : SSet.{u})) =
      snd (SSet.boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        prodStdSimplex₁.ι (0 : Fin 1) ≫
          (yonedaEquiv.symm x ▷ (Δ[1] : SSet.{u})) := by
  apply CartesianMonoidalCategory.hom_ext
  · have h₁ :
        SSet.const
          (X := (SSet.boundary n : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) x =
          snd (SSet.boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            SSet.stdSimplex.σ (0 : Fin 1) ≫ yonedaEquiv.symm x := by
      calc SSet.const
            (X := (SSet.boundary n : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) x
          = snd (SSet.boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
              SSet.const (X := (Δ[1] : SSet.{u})) x := by
            simp only [SSet.comp_const]
        _ = snd _ _ ≫
              (SSet.stdSimplex.σ (0 : Fin 1) ≫ yonedaEquiv.symm x) := by
            simp only [SSet.yonedaEquiv_symm_zero, SSet.comp_const]
        _ = snd _ _ ≫ SSet.stdSimplex.σ (0 : Fin 1) ≫
              yonedaEquiv.symm x := rfl
    calc (SSet.const
          (X := (SSet.boundary n : SSet.{u})) x ▷
            (Δ[1] : SSet.{u})) ≫ fst _ _
        = SSet.const
            (X := (SSet.boundary n : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) x := by
          simp [whiskerRight_fst]
      _ = snd _ _ ≫ SSet.stdSimplex.σ (0 : Fin 1) ≫
            yonedaEquiv.symm x := h₁
      _ = (snd _ _ ≫ prodStdSimplex₁.ι (0 : Fin 1) ≫
            (yonedaEquiv.symm x ▷ (Δ[1] : SSet.{u}))) ≫ fst _ _ := by
          simp [Category.assoc]
  · have h₂ :
        snd (SSet.boundary n : SSet.{u}) (Δ[1] : SSet.{u}) =
          snd (SSet.boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            yonedaEquiv.symm
              (SSet.stdSimplex.objMk₁
                (Fin.castSucc (0 : Fin 1)).succ) := by
      have h_id :
          yonedaEquiv.symm
            (SSet.stdSimplex.objMk₁ (Fin.castSucc (0 : Fin 1)).succ :
              (Δ[1] : SSet.{u}) _⦋1⦌) = 𝟙 _ := by
        apply SSet.yonedaEquiv.injective
        ext i
        fin_cases i <;> rfl
      calc snd (SSet.boundary n : SSet.{u}) (Δ[1] : SSet.{u})
          = snd _ _ ≫ 𝟙 _ := by simp
        _ = snd _ _ ≫
              yonedaEquiv.symm
                (SSet.stdSimplex.objMk₁
                  (Fin.castSucc (0 : Fin 1)).succ) := by
            rw [h_id]
    calc (SSet.const
          (X := (SSet.boundary n : SSet.{u})) x ▷
            (Δ[1] : SSet.{u})) ≫ snd _ _
        = snd _ _ := by simp [whiskerRight_snd]
      _ = (snd _ _ ≫ prodStdSimplex₁.ι (0 : Fin 1) ≫
            (yonedaEquiv.symm x ▷ (Δ[1] : SSet.{u}))) ≫ snd _ _ := by
          calc snd _ _
              = snd _ _ ≫
                  yonedaEquiv.symm
                    (SSet.stdSimplex.objMk₁
                      (Fin.castSucc (0 : Fin 1)).succ) := h₂
            _ = snd _ _ ≫
                  (prodStdSimplex₁.ι (0 : Fin 1) ≫ snd _ _) := by
                rw [← SSet.prodStdSimplex₁.ι_snd]
            _ = snd _ _ ≫ prodStdSimplex₁.ι (0 : Fin 1) ≫
                  snd _ _ := by rw [← Category.assoc]
            _ = snd _ _ ≫ prodStdSimplex₁.ι (0 : Fin 1) ≫
                  ((yonedaEquiv.symm x ▷ (Δ[1] : SSet.{u})) ≫
                    snd _ _) := by
                rw [← whiskerRight_snd
                  (f := yonedaEquiv.symm x) (Z := (Δ[1] : SSet.{u}))]
            _ = (snd _ _ ≫ prodStdSimplex₁.ι (0 : Fin 1) ≫
                  (yonedaEquiv.symm x ▷ (Δ[1] : SSet.{u}))) ≫
                  snd _ _ := rfl

noncomputable def ActionStruct.ofHomotopy :
    ActionStruct
      (SSet.Edge.ofSimplicialObjectHomotopy
        H.toSimplicialObjectHomotopy x)
      (SSet.PtSimplex.map f rfl s) (SSet.PtSimplex.map g rfl s) where
  prism := (SSet.RelativeMorphism.map s ▷ (Δ[1] : SSet.{u})) ≫ H.h
  boundary := by
    calc (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫
          ((SSet.RelativeMorphism.map s ▷ (Δ[1] : SSet.{u})) ≫ H.h)
        = ((SSet.boundary n).ι ≫ SSet.RelativeMorphism.map s) ▷
            (Δ[1] : SSet.{u}) ≫ H.h := by
          rw [← comp_whiskerRight_assoc]
      _ = (SSet.const
            (X := (SSet.boundary n : SSet.{u}))
            (Y := SSet.Subcomplex.ofSimplex x)
            ⟨x, Subcomplex.mem_ofSimplex_obj (X := X) x⟩ ≫
            (SSet.Subcomplex.ofSimplex x).ι) ▷
            (Δ[1] : SSet.{u}) ≫ H.h := by
          rw [s.comm]
      _ = (SSet.const (X := (SSet.boundary n : SSet.{u})) x ▷
            (Δ[1] : SSet.{u})) ≫ H.h := by
          rw [Subcomplex.ofSimplex_ι, comp_const]
      _ = snd (SSet.boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            prodStdSimplex₁.ι (0 : Fin 1) ≫
              (yonedaEquiv.symm x ▷ (Δ[1] : SSet.{u}) ≫ H.h) := by
          rw [const_cylinder (x := x), Category.assoc, Category.assoc]
      _ = snd (SSet.boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫
            yonedaEquiv.symm
              (Edge.edge
                (Edge.ofSimplicialObjectHomotopy
                  H.toSimplicialObjectHomotopy x)) := by
          rw [Edge.ofSimplicialObjectHomotopy_edge]
          have h2 :
              H.toSimplicialObjectHomotopy.h 0 x =
                (yonedaEquiv.symm x ▷ (Δ[1] : SSet.{u}) ≫ H.h).app _
                  (prodStdSimplex₁.nonDegenerateEquiv
                    (0 : Fin 1)).1 := rfl
          rw [h2, ← yonedaEquiv_symm_comp]
          rfl
  left := by
    change (SSet.ι₀ : Δ[n] ⟶ Δ[n] ⊗ Δ[1]) ≫
      ((SSet.RelativeMorphism.map s ▷ (Δ[1] : SSet.{u})) ≫ H.h) =
      SSet.RelativeMorphism.map s ≫ f
    rw [← Category.assoc, SSet.ι₀_comp (SSet.RelativeMorphism.map s),
      Category.assoc, H.h₀]
  right := by
    change (SSet.ι₁ : Δ[n] ⟶ Δ[n] ⊗ Δ[1]) ≫
      ((SSet.RelativeMorphism.map s ▷ (Δ[1] : SSet.{u})) ≫ H.h) =
      SSet.RelativeMorphism.map s ≫ g
    rw [← Category.assoc, SSet.ι₁_comp (SSet.RelativeMorphism.map s),
      Category.assoc, H.h₁]

end FundamentalGroupoid

namespace π

variable {X Y : SSet.{u}} [KanComplex Y] {f g : X ⟶ Y}

lemma action_map_eq_map_of_homotopy (H : Homotopy f g)
    {n : ℕ} {x : X _⦋0⦌} (q : π n X x) :
    π.action
      ((SSet.congrMapFundamentalGroupoid H).hom.app
        (SSet.FundamentalGroupoid.mk x))
      (π.map f rfl n q) = π.map g rfl n q := by
  induction q using π.rec with
  | mk s =>
    simp only [π.map_mk]
    let hStruct :
        FundamentalGroupoid.ActionStruct
          (SSet.Edge.ofSimplicialObjectHomotopy
            H.toSimplicialObjectHomotopy x)
          (SSet.PtSimplex.map f rfl s)
          (SSet.PtSimplex.map g rfl s) :=
      FundamentalGroupoid.ActionStruct.ofHomotopy H s
    have hIso :
        (SSet.congrMapFundamentalGroupoid H).hom.app
          (SSet.FundamentalGroupoid.mk x) =
          SSet.FundamentalGroupoid.homMk
            (SSet.Edge.ofSimplicialObjectHomotopy
              H.toSimplicialObjectHomotopy x) := rfl
    rw [hIso]
    exact π.action_homMk_mk_eq_mk_of_actionStruct hStruct

end π

namespace W

theorem of_homotopy {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : Homotopy (f ≫ g) (𝟙 X)) (hY : Homotopy (g ≫ f) (𝟙 Y)) :
    W f := by
  have hFG :
      SSet.mapFundamentalGroupoid f ⋙ SSet.mapFundamentalGroupoid g ≅
        𝟭 (SSet.FundamentalGroupoid X) := by
    calc SSet.mapFundamentalGroupoid f ⋙ SSet.mapFundamentalGroupoid g
        ≅ SSet.mapFundamentalGroupoid (f ≫ g) :=
          SSet.mapFundamentalGroupoidComp f g
      _ ≅ SSet.mapFundamentalGroupoid (𝟙 X) :=
          SSet.congrMapFundamentalGroupoid hX
      _ ≅ 𝟭 (SSet.FundamentalGroupoid X) :=
          SSet.mapFundamentalGroupoidId X
  have hGF :
      SSet.mapFundamentalGroupoid g ⋙ SSet.mapFundamentalGroupoid f ≅
        𝟭 (SSet.FundamentalGroupoid Y) := by
    calc SSet.mapFundamentalGroupoid g ⋙ SSet.mapFundamentalGroupoid f
        ≅ SSet.mapFundamentalGroupoid (g ≫ f) :=
          SSet.mapFundamentalGroupoidComp g f
      _ ≅ SSet.mapFundamentalGroupoid (𝟙 Y) :=
          SSet.congrMapFundamentalGroupoid hY
      _ ≅ 𝟭 (SSet.FundamentalGroupoid Y) :=
          SSet.mapFundamentalGroupoidId Y
  have hEquiv : (SSet.mapFundamentalGroupoid f).IsEquivalence :=
    Functor.IsEquivalence.mk' (SSet.mapFundamentalGroupoid g)
      hFG.symm hGF
  have hBij :
      ∀ (n : ℕ) (x : X _⦋0⦌),
        Function.Bijective (π.map f rfl (n := n) (x := x)) := by
    intro n x
    let pX :=
      (SSet.congrMapFundamentalGroupoid hX).hom.app
        (SSet.FundamentalGroupoid.mk x)
    have hMapFGAction :
        ∀ (q : π n X x),
          π.action (n := n) pX
              (π.map (f ≫ g) rfl (n := n) (x := x) q) = q := by
      intro q
      have h1 :=
        π.action_map_eq_map_of_homotopy (f := f ≫ g) (g := 𝟙 X)
          (H := hX) (n := n) (x := x) (q := q)
      simpa only [π.map_id_apply] using h1
    have hfg_eq :
        g.app _ (f.app _ x) = (f ≫ g).app _ x := by
      simp
    have hMapFGComp :
        (π.map (f ≫ g) rfl (n := n) (x := x) :
          π n X x → π n X ((f ≫ g).app _ x)) =
          (π.map g hfg_eq n (x := f.app _ x) ∘
            π.map f rfl (n := n) (x := x)) := by
      funext q
      exact π.map_comp_apply (f := f) (g := g) (hx := rfl)
        (hy := hfg_eq) (h := rfl) (n := n) (x := x) (q := q)
    have hInjective :
        Function.Injective (π.map f rfl (n := n) (x := x)) := by
      have hLeftInverse :
          Function.LeftInverse
            (π.action (n := n) pX ∘ π.map g hfg_eq n (x := f.app _ x))
            (π.map f rfl (n := n) (x := x)) := by
        intro q
        calc (π.action (n := n) pX ∘ π.map g hfg_eq n (x := f.app _ x))
                (π.map f rfl (n := n) (x := x) q)
            = π.action (n := n) pX
                ((π.map g hfg_eq n (x := f.app _ x) ∘
                  π.map f rfl (n := n) (x := x)) q) := rfl
          _ = π.action (n := n) pX
                (π.map (f ≫ g) rfl (n := n) (x := x) q) := by
              rw [← hMapFGComp]
          _ = q := hMapFGAction q
      exact hLeftInverse.injective
    have hSurjective :
        Function.Surjective (π.map f rfl (n := n) (x := x)) := by
      let y : Y _⦋0⦌ := f.app _ x
      have hy : y = f.app _ x := rfl
      let pY :=
        (SSet.congrMapFundamentalGroupoid hY).hom.app
          (SSet.FundamentalGroupoid.mk y)
      have hMapGFAction :
          ∀ (q : π n Y y),
            π.action (n := n) pY
                (π.map (g ≫ f) rfl (n := n) (x := y) q) = q := by
        intro q
        have h1 :=
          π.action_map_eq_map_of_homotopy (f := g ≫ f) (g := 𝟙 Y)
            (H := hY) (n := n) (x := y) (q := q)
        simpa only [π.map_id_apply] using h1
      have hgf_y_eq :
          f.app _ (g.app _ y) = (g ≫ f).app _ y := by
        simp
      have hMapGFComp :
          (π.map (g ≫ f) rfl (n := n) (x := y) :
            π n Y y → π n Y ((g ≫ f).app _ y)) =
            (π.map f hgf_y_eq n (x := g.app _ y) ∘
              π.map g rfl (n := n) (x := y)) := by
        funext q
        exact π.map_comp_apply (f := g) (g := f) (hx := rfl)
          (hy := hgf_y_eq) (h := rfl) (n := n) (x := y) (q := q)
      have hBijGF :
          Function.Bijective
            (π.map (g ≫ f) rfl (n := n) (x := y) :
              π n Y y → π n Y ((g ≫ f).app _ y)) := by
        have hCompBijective :
            Function.Bijective
              (π.action (n := n) pY ∘
                π.map (g ≫ f) rfl (n := n) (x := y)) := by
          have hEq :
              π.action (n := n) pY ∘
                π.map (g ≫ f) rfl (n := n) (x := y) = _root_.id := by
            funext q
            exact hMapGFAction q
          rw [hEq]
          exact Function.bijective_id
        exact
          (Function.Bijective.of_comp_iff' (π.action_bijective pY) _).mp
            hCompBijective
      have hSurjectiveAtG :
          Function.Surjective
            (π.map f hgf_y_eq n (x := g.app _ y) :
              π n X (g.app _ y) →
                π n Y ((g ≫ f).app _ y)) := by
        intro q
        obtain ⟨r, hr⟩ := hBijGF.2 q
        refine ⟨π.map g rfl n r, ?_⟩
        calc π.map f hgf_y_eq n (π.map g rfl n r)
            = (π.map f hgf_y_eq n ∘ π.map g rfl n) r := rfl
          _ = π.map (g ≫ f) rfl n r := by
              rw [← hMapGFComp]
          _ = q := hr
      have hObjFG :
          (SSet.mapFundamentalGroupoid (f ≫ g)).obj
              (SSet.FundamentalGroupoid.mk x) =
            SSet.FundamentalGroupoid.mk ((f ≫ g).app _ x) := by
        simp [SSet.mapFundamentalGroupoid_obj_mk]
      have hObjId :
          (SSet.mapFundamentalGroupoid (𝟙 X)).obj
              (SSet.FundamentalGroupoid.mk x) =
            SSet.FundamentalGroupoid.mk x := by
        simp [SSet.mapFundamentalGroupoid_obj_mk]
      have hSrcEq' :
          (SSet.mapFundamentalGroupoid (f ≫ g)).obj
              (SSet.FundamentalGroupoid.mk x) =
            SSet.FundamentalGroupoid.mk (g.app _ y) := by
        simp [SSet.mapFundamentalGroupoid_obj_mk, y]
      let pX' : SSet.FundamentalGroupoid.mk (g.app _ y) ⟶
          SSet.FundamentalGroupoid.mk x :=
        eqToHom hSrcEq' ≫ pX ≫ eqToHom hObjId
      have hfx_y : f.app _ x = y := rfl
      have hNaturality :
          ∀ (q : π n X (g.app _ y)),
            π.map f hfx_y n (x := x) (π.action (n := n) pX' q) =
              π.action (n := n)
                  ((SSet.mapFundamentalGroupoid f).map pX')
                (π.map f hgf_y_eq n (x := g.app _ y) q) := by
        intro q
        exact π.action_naturality f pX' q
      have hSurjectiveAtX :
          Function.Surjective
            (π.map f hfx_y n (x := x) :
              π n X x → π n Y y) := by
        intro qY
        have hActSurj :
            Function.Surjective
              (π.action (n := n)
                ((SSet.mapFundamentalGroupoid f).map pX') :
                π n Y ((g ≫ f).app _ y) → π n Y y) :=
          (π.action_bijective _).2
        obtain ⟨r, hr⟩ := hActSurj qY
        obtain ⟨s, hs⟩ := hSurjectiveAtG r
        refine ⟨π.action (n := n) pX' s, ?_⟩
        have h1 : π.map f hfx_y n (π.action (n := n) pX' s) =
            π.action (n := n)
                ((SSet.mapFundamentalGroupoid f).map pX')
              (π.map f hgf_y_eq n s) := hNaturality s
        have h2 :
            π.action (n := n)
                ((SSet.mapFundamentalGroupoid f).map pX')
                (π.map f hgf_y_eq n s) =
              π.action (n := n)
                ((SSet.mapFundamentalGroupoid f).map pX') r :=
          congrArg
            (π.action (n := n)
              ((SSet.mapFundamentalGroupoid f).map pX')) hs
        exact (h1.trans (h2.trans hr))
      have h_eq : hfx_y = rfl := by
        apply Subsingleton.elim
      have h_map_eq :
          π.map f hfx_y n (x := x) =
            π.map f rfl n (x := x) := by
        rw [h_eq]
      exact h_map_eq ▸ hSurjectiveAtX
    exact ⟨hInjective, hSurjective⟩
  exact W.mk f inferInstance inferInstance hEquiv hBij

/-- Homotopic maps between Kan complexes are weak equivalences
simultaneously. -/
theorem iff_of_homotopy {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    KanComplex.W f ↔ KanComplex.W g := by
  constructor
  · intro hf
    refine KanComplex.W.mk g inferInstance inferInstance ?_ ?_
    · let _ : (SSet.mapFundamentalGroupoid f).IsEquivalence :=
        KanComplex.W.isEquivalence_mapFundamentalGroupoid hf
      exact Functor.isEquivalence_of_iso
        (SSet.congrMapFundamentalGroupoid H)
    · intro n x
      let p := (SSet.congrMapFundamentalGroupoid H).hom.app
        (SSet.FundamentalGroupoid.mk x)
      have hMap :
          (KanComplex.π.map g rfl (n := n) (x := x)) =
            (KanComplex.π.action p) ∘
              KanComplex.π.map f rfl (n := n) (x := x) := by
        funext q
        exact (KanComplex.π.action_map_eq_map_of_homotopy
          (H := H) q).symm
      rw [hMap]
      exact Function.Bijective.comp
        (KanComplex.π.action_bijective p)
        (KanComplex.W.bijective_piMap hf n x)
  · intro hg
    refine KanComplex.W.mk f inferInstance inferInstance ?_ ?_
    · let _ : (SSet.mapFundamentalGroupoid g).IsEquivalence :=
        KanComplex.W.isEquivalence_mapFundamentalGroupoid hg
      exact Functor.isEquivalence_of_iso
        (SSet.congrMapFundamentalGroupoid H).symm
    · intro n x
      let p := (SSet.congrMapFundamentalGroupoid H).hom.app
        (SSet.FundamentalGroupoid.mk x)
      have hMap :
          (KanComplex.π.map g rfl (n := n) (x := x)) =
            (KanComplex.π.action p) ∘
              KanComplex.π.map f rfl (n := n) (x := x) := by
        funext q
        exact (KanComplex.π.action_map_eq_map_of_homotopy
          (H := H) q).symm
      have hComp : Function.Bijective
          ((KanComplex.π.action p) ∘
            KanComplex.π.map f rfl (n := n) (x := x)) := by
        rw [← hMap]
        exact KanComplex.W.bijective_piMap hg n x
      exact (Function.Bijective.of_comp_iff'
        (KanComplex.π.action_bijective p) _).mp hComp

end W

end KanComplex

end SSet

end
