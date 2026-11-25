/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.GoodCellExtensionInitialEmbedding

/-!
# Actual original-vertex lower comparison descenders

A prior actual vertex comparison and the original strict predecessor
cofan construct every lower-to-original-predecessor map. All cofan legs,
root equations and support inclusions use the same original descenders.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.OriginalCellVertexLowerComparison

open Limits LowerSetColimits

variable {C : Type u} [Category.{v} C]
  {Q P : Type w} [PartialOrder Q] [PartialOrder P]
  {A : Type t} {s : A → Arrow C} {X : C}
  (G : CellTree s X (P := Q)) (L : LowerSetColimitData G.diagram)
  (O : CellTree s X (P := P)) (f : Q →o P)
  (beta : G.diagram ⟶ f.monotone.functor ⋙ O.diagram)
  (t : P) (B : LowerSet Q) (hPred : ∀ q : Q, q ∈ B → f q < t)

/-- The lower comparison cocone retains the old vertex maps and original predecessor legs. -/
def cocone : Cocone (restriction G.diagram B) where
  pt := O.predecessorObj t
  ι :=
    { app q := beta.app q.1 ≫ (O.predecessor t).cocone.ι.app ⟨f q.1, hPred q.1 q.2⟩
      naturality q r h := by
        have hqr : q.1 ≤ r.1 := leOfHom h
        let h' : q.1 ⟶ r.1 := homOfLE hqr
        let oldh : (⟨f q.1, hPred q.1 q.2⟩ : LowerSet.Iio t) ⟶
            ⟨f r.1, hPred r.1 r.2⟩ := homOfLE (f.monotone hqr)
        let legQ : O.vertex (f q.1) ⟶ O.predecessorObj t :=
          (O.predecessor t).cocone.ι.app ⟨f q.1, hPred q.1 q.2⟩
        let legR : O.vertex (f r.1) ⟶ O.predecessorObj t :=
          (O.predecessor t).cocone.ι.app ⟨f r.1, hPred r.1 r.2⟩
        have hp : (f.monotone.functor ⋙ O.diagram).map h' ≫ legR = legQ :=
          (O.predecessor t).cocone.w oldh
        have hn : G.diagram.map h' ≫ beta.app r.1 =
            beta.app q.1 ≫ (f.monotone.functor ⋙ O.diagram).map h' := beta.naturality h'
        change G.diagram.map h' ≫
            (beta.app r.1 ≫ (O.predecessor t).cocone.ι.app ⟨f r.1, hPred r.1 r.2⟩) =
          (beta.app q.1 ≫ (O.predecessor t).cocone.ι.app ⟨f q.1, hPred q.1 q.2⟩) ≫ 𝟙 _
        calc
          _ = (G.diagram.map h' ≫ beta.app r.1) ≫ legR := (Category.assoc _ _ _).symm
          _ = (beta.app q.1 ≫ (f.monotone.functor ⋙ O.diagram).map h') ≫ legR :=
            congrArg (fun k => k ≫ legR) hn
          _ = beta.app q.1 ≫ ((f.monotone.functor ⋙ O.diagram).map h' ≫ legR) :=
            Category.assoc _ _ _
          _ = beta.app q.1 ≫ legQ := congrArg (fun k => beta.app q.1 ≫ k) hp
          _ = _ := (Category.comp_id _).symm }

/-- The actual original lower-to-predecessor map is the same selected L colimit descender. -/
def lowerMap : L.obj B ⟶ O.predecessorObj t :=
  (L.isColimit B).desc (cocone G O f beta t B hPred)

/-- Every complete original lower cofan leg retains its actual original vertex comparison. -/
@[reassoc]
theorem lowerMap_fac (q : B) :
    L.ι B q ≫ lowerMap G L O f beta t B hPred =
      beta.app q.1 ≫ (O.predecessor t).cocone.ι.app ⟨f q.1, hPred q.1 q.2⟩ :=
  (L.isColimit B).fac (cocone G O f beta t B hPred) q

/-- The whole lower comparison keeps its original root under the same arbitrary source. -/
theorem lowerMap_root :
    (L.obj B).hom ≫ (lowerMap G L O f beta t B hPred).right = (O.predecessorObj t).hom :=
  Under.w (lowerMap G L O f beta t B hPred)

/-- The same original comparison descenders commute with every actual lower-support inclusion. -/
theorem lowerMap_inclusion (E : LowerSet Q) (hEB : E ≤ B) :
    L.map hEB ≫ lowerMap G L O f beta t B hPred =
      lowerMap G L O f beta t E (fun q hq => hPred q (hEB hq)) := by
  apply (L.isColimit E).hom_ext
  intro q
  rw [← Category.assoc, L.ι_map, lowerMap_fac, lowerMap_fac]

end CategoryTheory.SmallObject.OriginalCellVertexLowerComparison
