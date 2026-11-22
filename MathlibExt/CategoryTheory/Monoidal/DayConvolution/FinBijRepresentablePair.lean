/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FinBijRepresentableTensor

/-!
# Two representables under finite-bijection Day convolution

The second collapse keeps every original finite-bijection label. At a
decomposition `a ⊗ s ⟶ q`, the generator `r ⟶ a` maps to its ordered-block
composite `r ⊗ s ⟶ q`. The inverse uses the original identity generator and
the original colimit leg. Coefficients retain the order `M ⊗ N`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.Operad.SmallFinBijGroupoid.RepresentablePair

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  [HasColimitsOfSize.{0, 0} V]

/-- The second, complement-first decomposition diagram. -/
abbrev diagram (r s q : SmallFinBijGroupoid) (M N : V) :
    BlockDecomposition s q ⥤ V :=
  CostructuredArrow.proj (tensorRight s) q ⋙
    (evaluationLeftAdjoint V r).obj M ⋙ tensorRight N

/-- The coproduct indexed by the actual ordered-block bijections. -/
abbrev representedComponent (r s q : SmallFinBijGroupoid) (M N : V) : V :=
  ((evaluationLeftAdjoint V (r ⊗ s)).obj (M ⊗ N)).obj q

/-- The generator map before the second colimit descent. -/
def collapseLeg (r s q : SmallFinBijGroupoid) (M N : V)
    [PreservesColimitsOfSize.{0, 0} (tensorRight N)] (d : BlockDecomposition s q) :
    (diagram r s q M N).obj d ⟶ representedComponent r s q M N :=
  (PreservesCoproduct.iso (tensorRight N)
      (fun _ : r ⟶ d.left => M)).hom ≫
    Sigma.desc (fun α =>
      Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) ((α ▷ s) ≫ d.hom))

private theorem tensorRight_coproduct_generator
    {J : Type} (M N : V)
    [PreservesColimitsOfSize.{0, 0} (tensorRight N)] (j : J) :
    (Sigma.ι (fun _ : J => M) j ▷ N) ≫
      (PreservesCoproduct.iso (tensorRight N) (fun _ : J => M)).hom =
    Sigma.ι (fun _ : J => M ⊗ N) j := by
  apply (cancel_mono
    (PreservesCoproduct.iso (tensorRight N) (fun _ : J => M)).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    PreservesCoproduct.inv_hom]
  exact (ι_comp_sigmaComparison (tensorRight N) (fun _ : J => M) j).symm

/-- The second collapse sends every actual generator to its full block label. -/
@[reassoc]
theorem collapseLeg_generator
    (r s q : SmallFinBijGroupoid) (M N : V)
    [PreservesColimitsOfSize.{0, 0} (tensorRight N)]
    (d : BlockDecomposition s q) (α : r ⟶ d.left) :
    (Sigma.ι (fun _ : r ⟶ d.left => M) α ▷ N) ≫
      collapseLeg r s q M N d =
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) ((α ▷ s) ≫ d.hom) := by
  dsimp [collapseLeg, diagram, representedComponent, evaluationLeftAdjoint]
  rw [← Category.assoc, tensorRight_coproduct_generator,
    Sigma.ι_comp_desc]

omit [MonoidalCategory V] in
private theorem represented_generator_map
    (r : SmallFinBijGroupoid) (M : V)
    {a b : SmallFinBijGroupoid} (g : a ⟶ b) (α : r ⟶ a) :
    Sigma.ι (fun _ : r ⟶ a => M) α ≫
      ((evaluationLeftAdjoint V r).obj M).map g =
    Sigma.ι (fun _ : r ⟶ b => M) (α ≫ g) := by
  dsimp [evaluationLeftAdjoint]
  exact Sigma.ι_comp_desc _ _

private theorem diagram_generator_map
    (r s q : SmallFinBijGroupoid) (M N : V)
    {d e : BlockDecomposition s q} (g : d ⟶ e) (α : r ⟶ d.left) :
    (Sigma.ι (fun _ : r ⟶ d.left => M) α ▷ N) ≫
      (diagram r s q M N).map g =
    Sigma.ι (fun _ : r ⟶ e.left => M) (α ≫ g.left) ▷ N := by
  dsimp [diagram, evaluationLeftAdjoint]
  rw [← comp_whiskerRight, Sigma.ι_comp_desc]

/-- The second collapse respects the original costructured-arrow relations. -/
def collapseCocone (r s q : SmallFinBijGroupoid) (M N : V)
    [PreservesColimitsOfSize.{0, 0} (tensorRight N)] :
    Cocone (diagram r s q M N) where
  pt := representedComponent r s q M N
  ι :=
    { app := collapseLeg r s q M N
      naturality := by
        intro d e g
        dsimp [diagram, representedComponent, evaluationLeftAdjoint]
        apply (cancel_epi
          (PreservesCoproduct.iso (tensorRight N)
            (fun _ : r ⟶ d.left => M)).inv).1
        apply Sigma.hom_ext
        intro α
        rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc,
          ι_comp_sigmaComparison_assoc]
        change (Sigma.ι (fun _ : r ⟶ d.left => M) α ▷ N) ≫
          (diagram r s q M N).map g ≫ collapseLeg r s q M N e =
          (Sigma.ι (fun _ : r ⟶ d.left => M) α ▷ N) ≫
            collapseLeg r s q M N d ≫ 𝟙 _
        let jd : M ⊗ N ⟶ (diagram r s q M N).obj d :=
          Sigma.ι (fun _ : r ⟶ d.left => M) α ▷ N
        let je : M ⊗ N ⟶ (diagram r s q M N).obj e :=
          Sigma.ι (fun _ : r ⟶ e.left => M) (α ≫ g.left) ▷ N
        let κ (h : r ⊗ s ⟶ q) : M ⊗ N ⟶ representedComponent r s q M N :=
          Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) h
        have hg : jd ≫ (diagram r s q M N).map g = je :=
          diagram_generator_map r s q M N g α
        have hlabel : ((α ≫ g.left) ▷ s) ≫ e.hom = (α ▷ s) ≫ d.hom := by
          rw [comp_whiskerRight, Category.assoc]
          exact congrArg (fun k => (α ▷ s) ≫ k) (CostructuredArrow.w g)
        change jd ≫ (diagram r s q M N).map g ≫ collapseLeg r s q M N e =
          jd ≫ collapseLeg r s q M N d ≫ 𝟙 _
        calc
          jd ≫ (diagram r s q M N).map g ≫ collapseLeg r s q M N e =
              (jd ≫ (diagram r s q M N).map g) ≫ collapseLeg r s q M N e :=
            (Category.assoc _ _ _).symm
          _ = je ≫ collapseLeg r s q M N e :=
            congrArg (fun k => k ≫ collapseLeg r s q M N e) hg
          _ = κ (((α ≫ g.left) ▷ s) ≫ e.hom) :=
            collapseLeg_generator r s q M N e (α ≫ g.left)
          _ = κ ((α ▷ s) ≫ d.hom) := congrArg κ hlabel
          _ = jd ≫ collapseLeg r s q M N d ≫ 𝟙 _ := by
            rw [Category.comp_id]
            exact (collapseLeg_generator r s q M N d α).symm }

/-- The actual colimit descent for the second collapse. -/
def forward (r s q : SmallFinBijGroupoid) (M N : V)
    [PreservesColimitsOfSize.{0, 0} (tensorRight N)] :
    colimit (diagram r s q M N) ⟶ representedComponent r s q M N :=
  colimit.desc (diagram r s q M N) (collapseCocone r s q M N)

/-- The identity-block decomposition for a full ordered-block label. -/
abbrev identityDecomposition (r s q : SmallFinBijGroupoid)
    (h : r ⊗ s ⟶ q) : BlockDecomposition s q :=
  CostructuredArrow.mk (Y := r) h

/-- The inverse sends an actual block label to the original identity generator. -/
def backward (r s q : SmallFinBijGroupoid) (M N : V) :
    representedComponent r s q M N ⟶ colimit (diagram r s q M N) :=
  Sigma.desc (fun h =>
    (Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r) ▷ N) ≫
      colimit.ι (diagram r s q M N) (identityDecomposition r s q h))

/-- Forward descent on an arbitrary original generator. -/
@[reassoc]
theorem forward_generator
    (r s q : SmallFinBijGroupoid) (M N : V)
    [PreservesColimitsOfSize.{0, 0} (tensorRight N)]
    (d : BlockDecomposition s q) (α : r ⟶ d.left) :
    (Sigma.ι (fun _ : r ⟶ d.left => M) α ▷ N) ≫
      colimit.ι (diagram r s q M N) d ≫ forward r s q M N =
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) ((α ▷ s) ≫ d.hom) := by
  let j : M ⊗ N ⟶ (diagram r s q M N).obj d :=
    Sigma.ι (fun _ : r ⟶ d.left => M) α ▷ N
  change j ≫ colimit.ι (diagram r s q M N) d ≫
    colimit.desc (diagram r s q M N) (collapseCocone r s q M N) = _
  rw [colimit.ι_desc]
  exact collapseLeg_generator r s q M N d α

/-- Inverse descent on an arbitrary original block label. -/
@[reassoc]
theorem backward_generator (r s q : SmallFinBijGroupoid) (M N : V)
    (h : r ⊗ s ⟶ q) :
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) h ≫ backward r s q M N =
    (Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r) ▷ N) ≫
      colimit.ι (diagram r s q M N) (identityDecomposition r s q h) := by
  dsimp only [backward, representedComponent, evaluationLeftAdjoint]
  exact Sigma.ι_comp_desc _ _

/-- The original costructured-arrow relation contracts an arbitrary left label. -/
@[reassoc]
theorem identity_generator_relation
    (r s q : SmallFinBijGroupoid) (M N : V)
    (d : BlockDecomposition s q) (α : r ⟶ d.left) :
    (Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r) ▷ N) ≫
      colimit.ι (diagram r s q M N)
        (identityDecomposition r s q ((α ▷ s) ≫ d.hom)) =
    (Sigma.ι (fun _ : r ⟶ d.left => M) α ▷ N) ≫
      colimit.ι (diagram r s q M N) d := by
  let g : identityDecomposition r s q ((α ▷ s) ≫ d.hom) ⟶ d :=
    CostructuredArrow.homMk α rfl
  rw [← colimit.w (diagram r s q M N) g]
  dsimp [diagram, evaluationLeftAdjoint]
  rw [← Category.assoc, ← comp_whiskerRight, Sigma.ι_comp_desc]
  simp only [Category.id_comp]
  rfl

/-- Both second-collapse maps compose to the actual represented identity. -/
theorem backward_forward
    (r s q : SmallFinBijGroupoid) (M N : V)
    [PreservesColimitsOfSize.{0, 0} (tensorRight N)] :
    backward r s q M N ≫ forward r s q M N =
      𝟙 (representedComponent r s q M N) := by
  apply Sigma.hom_ext
  intro h
  let κ (k : r ⊗ s ⟶ q) : M ⊗ N ⟶ representedComponent r s q M N :=
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) k
  let j : M ⊗ N ⟶ representedComponent r s q M N :=
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) h
  change j ≫ backward r s q M N ≫ forward r s q M N = j ≫ 𝟙 _
  calc
    j ≫ backward r s q M N ≫ forward r s q M N =
        (j ≫ backward r s q M N) ≫ forward r s q M N :=
      (Category.assoc _ _ _).symm
    _ = ((Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r) ▷ N) ≫
          colimit.ι (diagram r s q M N) (identityDecomposition r s q h)) ≫
        forward r s q M N :=
      congrArg (fun k => k ≫ forward r s q M N)
        (backward_generator r s q M N h)
    _ = (Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r) ▷ N) ≫
          colimit.ι (diagram r s q M N) (identityDecomposition r s q h) ≫
        forward r s q M N := Category.assoc _ _ _
    _ = κ ((𝟙 r ▷ s) ≫ h) :=
      forward_generator r s q M N (identityDecomposition r s q h) (𝟙 r)
    _ = j ≫ 𝟙 _ := by
      change κ ((𝟙 r ▷ s) ≫ h) = κ h ≫ 𝟙 _
      simp only [id_whiskerRight, Category.id_comp, Category.comp_id]

/-- Both second-collapse maps compose to the actual colimit identity. -/
theorem forward_backward
    (r s q : SmallFinBijGroupoid) (M N : V)
    [PreservesColimitsOfSize.{0, 0} (tensorRight N)] :
    forward r s q M N ≫ backward r s q M N =
      𝟙 (colimit (diagram r s q M N)) := by
  apply colimit.hom_ext
  intro d
  let p : (diagram r s q M N).obj d ≅
      ∐ (fun _ : r ⟶ d.left => M ⊗ N) :=
    PreservesCoproduct.iso (tensorRight N) (fun _ : r ⟶ d.left => M)
  apply (cancel_epi
    p.inv).1
  apply Sigma.hom_ext
  intro α
  let j : M ⊗ N ⟶ (diagram r s q M N).obj d :=
    Sigma.ι (fun _ : r ⟶ d.left => M) α ▷ N
  have hσ : Sigma.ι (fun _ : r ⟶ d.left => M ⊗ N) α ≫ p.inv = j :=
    ι_comp_sigmaComparison (tensorRight N) (fun _ : r ⟶ d.left => M) α
  simp only [← Category.assoc, hσ]
  simp only [Category.assoc]
  calc
    j ≫ colimit.ι (diagram r s q M N) d ≫ forward r s q M N ≫
        backward r s q M N =
      (j ≫ colimit.ι (diagram r s q M N) d ≫ forward r s q M N) ≫
        backward r s q M N := by simp only [Category.assoc]
    _ = Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) ((α ▷ s) ≫ d.hom) ≫
        backward r s q M N :=
      congrArg (fun k => k ≫ backward r s q M N)
        (forward_generator r s q M N d α)
    _ = _ := backward_generator r s q M N ((α ▷ s) ≫ d.hom)
    _ = j ≫ colimit.ι (diagram r s q M N) d :=
      identity_generator_relation r s q M N d α
    _ = j ≫ colimit.ι (diagram r s q M N) d ≫ 𝟙 _ := by
      rw [Category.comp_id]

/-- The actual second collapse, without a supplied pair comparison. -/
def componentIso (r s q : SmallFinBijGroupoid) (M N : V)
    [PreservesColimitsOfSize.{0, 0} (tensorRight N)] :
    colimit (diagram r s q M N) ≅ representedComponent r s q M N where
  hom := forward r s q M N
  inv := backward r s q M N
  hom_inv_id := forward_backward r s q M N
  inv_hom_id := backward_forward r s q M N

omit [HasColimitsOfSize.{0, 0} V] in
private theorem tensor_square
    {M M' P P' N N' : V} (j : M ⟶ P) (j' : M' ⟶ P')
    (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P') (w : j ≫ h = f ≫ j') :
    (j ▷ N) ≫ (h ⊗ₘ g) = (f ⊗ₘ g) ≫ (j' ▷ N') := by
  simpa only [← tensorHom_id, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id] using congrArg (fun k => k ⊗ₘ g) w

/-- Both coefficient arrows act on the actual second decomposition diagram. -/
def coefficientMap (r s q : SmallFinBijGroupoid)
    {M M' N N' : V} (f : M ⟶ M') (g : N ⟶ N') :
    diagram r s q M N ⟶ diagram r s q M' N' where
  app d := ((evaluationLeftAdjoint V r).map f).app d.left ⊗ₘ g
  naturality {d e} k := by
    change (((evaluationLeftAdjoint V r).obj M).map k.left ▷ N) ≫
        (((evaluationLeftAdjoint V r).map f).app e.left ⊗ₘ g) =
      (((evaluationLeftAdjoint V r).map f).app d.left ⊗ₘ g) ≫
        (((evaluationLeftAdjoint V r).obj M').map k.left ▷ N')
    simpa only [← tensorHom_id, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id] using
      congrArg (fun h => h ⊗ₘ g) (((evaluationLeftAdjoint V r).map f).naturality k.left)

omit [MonoidalCategory V] in
private theorem represented_generator_coefficient
    (r a : SmallFinBijGroupoid) {M M' : V} (f : M ⟶ M') (α : r ⟶ a) :
    Sigma.ι (fun _ : r ⟶ a => M) α ≫
      ((evaluationLeftAdjoint V r).map f).app a =
    f ≫ Sigma.ι (fun _ : r ⟶ a => M') α := by
  dsimp [evaluationLeftAdjoint]
  exact Sigma.ι_comp_desc _ _

/-- Both coefficient maps preserve every original decomposition generator. -/
@[reassoc]
theorem coefficientMap_generator (r s q : SmallFinBijGroupoid)
    {M M' N N' : V} (f : M ⟶ M') (g : N ⟶ N')
    (d : BlockDecomposition s q) (α : r ⟶ d.left) :
    (Sigma.ι (fun _ : r ⟶ d.left => M) α ▷ N) ≫
      (coefficientMap r s q f g).app d =
    (f ⊗ₘ g) ≫ (Sigma.ι (fun _ : r ⟶ d.left => M') α ▷ N') := by
  exact tensor_square _ _ f g _ (represented_generator_coefficient r d.left f α)

/-- Inverse second collapse is natural simultaneously in both coefficients.
No tensor-colimit preservation is needed for this identity. -/
theorem backward_coefficient (r s q : SmallFinBijGroupoid)
    {M M' N N' : V} (f : M ⟶ M') (g : N ⟶ N') :
    ((evaluationLeftAdjoint V (r ⊗ s)).map (f ⊗ₘ g)).app q ≫
        backward r s q M' N' =
      backward r s q M N ≫ colim.map (coefficientMap r s q f g) := by
  apply Sigma.hom_ext
  intro h
  let d := identityDecomposition r s q h
  let κ : M ⊗ N ⟶ representedComponent r s q M N :=
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) h
  let κ' : M' ⊗ N' ⟶ representedComponent r s q M' N' :=
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M' ⊗ N') h
  let j : M ⊗ N ⟶ (diagram r s q M N).obj d :=
    Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r) ▷ N
  let j' : M' ⊗ N' ⟶ (diagram r s q M' N').obj d :=
    Sigma.ι (fun _ : r ⟶ r => M') (𝟙 r) ▷ N'
  have hκ : κ ≫ ((evaluationLeftAdjoint V (r ⊗ s)).map (f ⊗ₘ g)).app q =
      (f ⊗ₘ g) ≫ κ' := represented_generator_coefficient (r ⊗ s) q (f ⊗ₘ g) h
  have hj : j ≫ (coefficientMap r s q f g).app d = (f ⊗ₘ g) ≫ j' :=
    coefficientMap_generator r s q f g d (𝟙 r)
  have hκj : κ ≫ backward r s q M N = j ≫ colimit.ι (diagram r s q M N) d :=
    backward_generator r s q M N h
  have hκj' : κ' ≫ backward r s q M' N' = j' ≫ colimit.ι (diagram r s q M' N') d :=
    backward_generator r s q M' N' h
  have hmap : colimit.ι (diagram r s q M N) d ≫ colim.map (coefficientMap r s q f g) =
      (coefficientMap r s q f g).app d ≫ colimit.ι (diagram r s q M' N') d :=
    colimit.ι_map (coefficientMap r s q f g) d
  change κ ≫ ((evaluationLeftAdjoint V (r ⊗ s)).map (f ⊗ₘ g)).app q ≫
      backward r s q M' N' =
    κ ≫ backward r s q M N ≫ colim.map (coefficientMap r s q f g)
  have hLeft : κ ≫ ((evaluationLeftAdjoint V (r ⊗ s)).map (f ⊗ₘ g)).app q ≫
      backward r s q M' N' =
      (f ⊗ₘ g) ≫ j' ≫ colimit.ι (diagram r s q M' N') d := by
    rw [← Category.assoc, hκ, Category.assoc, hκj']
  have hRight : κ ≫ backward r s q M N ≫ colim.map (coefficientMap r s q f g) =
      (f ⊗ₘ g) ≫ j' ≫ colimit.ι (diagram r s q M' N') d := by
    rw [← Category.assoc, hκj, Category.assoc, hmap,
      ← Category.assoc, hj, Category.assoc]
  exact hLeft.trans hRight.symm

omit [MonoidalCategory V] [HasColimitsOfSize.{0, 0} V] in
private theorem iso_forward_square
    {X Y X' Y' : V} (e : X ≅ Y) (e' : X' ≅ Y')
    (f : X ⟶ X') (g : Y ⟶ Y') (h : g ≫ e'.inv = e.inv ≫ f) :
    f ≫ e'.hom = e.hom ≫ g := by
  apply (cancel_mono e'.inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Category.assoc, h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Forward second collapse is natural simultaneously in both coefficients. -/
theorem forward_coefficient (r s q : SmallFinBijGroupoid)
    {M M' N N' : V} (f : M ⟶ M') (g : N ⟶ N')
    [PreservesColimitsOfSize.{0, 0} (tensorRight N)]
    [PreservesColimitsOfSize.{0, 0} (tensorRight N')] :
    colim.map (coefficientMap r s q f g) ≫ forward r s q M' N' =
      forward r s q M N ≫
        ((evaluationLeftAdjoint V (r ⊗ s)).map (f ⊗ₘ g)).app q := by
  exact iso_forward_square (componentIso r s q M N) (componentIso r s q M' N')
    (colim.map (coefficientMap r s q f g))
    (((evaluationLeftAdjoint V (r ⊗ s)).map (f ⊗ₘ g)).app q)
    (backward_coefficient r s q f g)

section IndexRelabeling

omit [MonoidalCategory V]

/-- Relabel a represented diagram by precomposition with the actual index arrow. -/
def indexMap {a b : SmallFinBijGroupoid} (k : a ⟶ b) (M : V) :
    (evaluationLeftAdjoint V b).obj M ⟶ (evaluationLeftAdjoint V a).obj M where
  app q := Sigma.desc (fun h => Sigma.ι (fun _ : a ⟶ q => M) (k ≫ h))
  naturality {q q'} τ := by
    dsimp [evaluationLeftAdjoint]
    apply Sigma.hom_ext
    intro h
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.assoc]

/-- Every actual source label is relabeled by the original index arrow. -/
@[reassoc]
theorem indexMap_generator {a b : SmallFinBijGroupoid} (k : a ⟶ b)
    (M : V) (q : SmallFinBijGroupoid) (h : b ⟶ q) :
    Sigma.ι (fun _ : b ⟶ q => M) h ≫ (indexMap k M).app q =
    Sigma.ι (fun _ : a ⟶ q => M) (k ≫ h) := by
  dsimp [indexMap, evaluationLeftAdjoint]
  exact Sigma.ι_comp_desc _ _

/-- Identity relabeling is the identity of the original represented functor. -/
theorem indexMap_id (a : SmallFinBijGroupoid) (M : V) :
    indexMap (𝟙 a) M = 𝟙 ((evaluationLeftAdjoint V a).obj M) := by
  ext q
  dsimp [indexMap, evaluationLeftAdjoint]
  apply Sigma.hom_ext
  intro h
  simp only [Sigma.ι_comp_desc, Category.id_comp, Category.comp_id]

/-- Contravariant composition uses the actual composite of the index arrows. -/
theorem indexMap_comp {a b c : SmallFinBijGroupoid}
    (k : a ⟶ b) (l : b ⟶ c) (M : V) :
    indexMap l M ≫ indexMap k M = indexMap (k ≫ l) M := by
  ext q
  dsimp [indexMap, evaluationLeftAdjoint]
  apply Sigma.hom_ext
  intro h
  simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.assoc]

/-- A genuine finite-bijection isomorphism relabels the entire represented diagram. -/
def indexIso {a b : SmallFinBijGroupoid} (e : a ≅ b) (M : V) :
    (evaluationLeftAdjoint V a).obj M ≅ (evaluationLeftAdjoint V b).obj M where
  hom := indexMap e.inv M
  inv := indexMap e.hom M
  hom_inv_id := by rw [indexMap_comp, e.hom_inv_id, indexMap_id]
  inv_hom_id := by rw [indexMap_comp, e.inv_hom_id, indexMap_id]

/-- Index relabeling commutes with the actual coefficient map. -/
theorem indexMap_coefficient {a b : SmallFinBijGroupoid} (k : a ⟶ b)
    {M M' : V} (f : M ⟶ M') :
    (evaluationLeftAdjoint V b).map f ≫ indexMap k M' =
      indexMap k M ≫ (evaluationLeftAdjoint V a).map f := by
  ext q
  dsimp [indexMap, evaluationLeftAdjoint]
  apply Sigma.hom_ext
  intro h
  simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.assoc]

end IndexRelabeling

/-- Switch the actual index blocks to the source order `s ⊗ r` while keeping
the coefficient order `M ⊗ N`. -/
def sourceOrderIso (r s : SmallFinBijGroupoid) (M N : V) :
    (evaluationLeftAdjoint V (r ⊗ s)).obj (M ⊗ N) ≅
      (evaluationLeftAdjoint V (s ⊗ r)).obj (M ⊗ N) :=
  indexIso (β_ r s) (M ⊗ N)

/-- The source-order comparison uses the actual inverse index braid on every label. -/
@[reassoc]
theorem sourceOrderIso_generator (r s q : SmallFinBijGroupoid) (M N : V)
    (h : r ⊗ s ⟶ q) :
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) h ≫ (sourceOrderIso r s M N).hom.app q =
    Sigma.ι (fun _ : s ⊗ r ⟶ q => M ⊗ N) ((β_ r s).inv ≫ h) := by
  exact indexMap_generator (β_ r s).inv (M ⊗ N) q h

/-- Both coefficient arrows commute with the full source-order comparison. -/
theorem sourceOrderIso_coefficient (r s : SmallFinBijGroupoid)
    {M M' N N' : V} (f : M ⟶ M') (g : N ⟶ N') :
    (evaluationLeftAdjoint V (r ⊗ s)).map (f ⊗ₘ g) ≫
        (sourceOrderIso r s M' N').hom =
      (sourceOrderIso r s M N).hom ≫
        (evaluationLeftAdjoint V (s ⊗ r)).map (f ⊗ₘ g) :=
  indexMap_coefficient (β_ r s).inv (f ⊗ₘ g)

section DayComparison

variable [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The original represented diagrams as a coefficient functor into Day functors. -/
def represented (r : SmallFinBijGroupoid) : V ⥤ DayFunctor SmallFinBijGroupoid V :=
  evaluationLeftAdjoint V r ⋙ (DayFunctor.equiv SmallFinBijGroupoid V).symm.functor

/-- Tensor the original identity generators and apply the original Day extension unit. -/
def dayGenerator (r s : SmallFinBijGroupoid) (M N : V) :
    M ⊗ N ⟶
      (((represented r).obj M ⊗ (represented s).obj N).functor.obj (r ⊗ s)) :=
  (Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r) ⊗ₘ
      Sigma.ι (fun _ : s ⟶ s => N) (𝟙 s)) ≫
    (DayFunctor.η ((represented r).obj M) ((represented s).obj N)).app (r, s)

/-- The original free/evaluation adjunct of the Day pair generator. Its
naturality retains every target finite bijection. -/
def dayInverse (r s : SmallFinBijGroupoid) (M N : V) :
    (represented (r ⊗ s)).obj (M ⊗ N) ⟶
      (represented r).obj M ⊗ (represented s).obj N :=
  DayFunctor.Hom.mk
    (((evaluationAdjunctionRight V (r ⊗ s)).homEquiv (M ⊗ N)
      (((represented r).obj M ⊗ (represented s).obj N).functor)).symm
        (dayGenerator r s M N))

/-- The full Day inverse on every original ordered-block label. -/
@[reassoc]
theorem dayInverse_generator (r s q : SmallFinBijGroupoid) (M N : V)
    (h : r ⊗ s ⟶ q) :
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) h ≫
        (dayInverse r s M N).natTrans.app q =
      dayGenerator r s M N ≫
        ((represented r).obj M ⊗ (represented s).obj N).functor.map h := by
  dsimp only [dayInverse, evaluationAdjunctionRight]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  dsimp only
  exact Sigma.ι_comp_desc _ _

omit [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
private theorem tensor_pair_square
    {M M' N N' P P' Q Q' : V}
    (j : M ⟶ P) (j' : M' ⟶ P') (k : N ⟶ Q) (k' : N' ⟶ Q')
    (f : M ⟶ M') (g : N ⟶ N') (a : P ⟶ P') (b : Q ⟶ Q')
    (hj : j ≫ a = f ≫ j') (hk : k ≫ b = g ≫ k') :
    (j ⊗ₘ k) ≫ (a ⊗ₘ b) = (f ⊗ₘ g) ≫ (j' ⊗ₘ k') := by
  rw [tensorHom_comp_tensorHom, hj, hk, ← tensorHom_comp_tensorHom]

/-- Simultaneous coefficient naturality of the original Day pair generator. -/
theorem dayGenerator_coefficient (r s : SmallFinBijGroupoid)
    {M M' N N' : V} (f : M ⟶ M') (g : N ⟶ N') :
    dayGenerator r s M N ≫
        ((represented r).map f ⊗ₘ (represented s).map g).natTrans.app (r ⊗ s) =
      (f ⊗ₘ g) ≫ dayGenerator r s M' N' := by
  let j : M ⟶ ((represented r).obj M).functor.obj r :=
    Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r)
  let j' : M' ⟶ ((represented r).obj M').functor.obj r :=
    Sigma.ι (fun _ : r ⟶ r => M') (𝟙 r)
  let k : N ⟶ ((represented s).obj N).functor.obj s :=
    Sigma.ι (fun _ : s ⟶ s => N) (𝟙 s)
  let k' : N' ⟶ ((represented s).obj N').functor.obj s :=
    Sigma.ι (fun _ : s ⟶ s => N') (𝟙 s)
  have hPair : (j ⊗ₘ k) ≫
      (((represented r).map f).natTrans.app r ⊗ₘ ((represented s).map g).natTrans.app s) =
      (f ⊗ₘ g) ≫ (j' ⊗ₘ k') :=
    tensor_pair_square j j' k k' f g _ _
      (represented_generator_coefficient r r f (𝟙 r))
      (represented_generator_coefficient s s g (𝟙 s))
  have hUnit :
      (DayFunctor.η ((represented r).obj M) ((represented s).obj N)).app (r, s) ≫
        ((represented r).map f ⊗ₘ (represented s).map g).natTrans.app (r ⊗ s) =
      (((represented r).map f).natTrans.app r ⊗ₘ ((represented s).map g).natTrans.app s) ≫
        (DayFunctor.η ((represented r).obj M') ((represented s).obj N')).app (r, s) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_tensorHom_app
      SmallFinBijGroupoid V ((represented r).map f) ((represented s).map g) r s
  change ((j ⊗ₘ k) ≫
      (DayFunctor.η ((represented r).obj M) ((represented s).obj N)).app (r, s)) ≫
        ((represented r).map f ⊗ₘ (represented s).map g).natTrans.app (r ⊗ s) =
    (f ⊗ₘ g) ≫ ((j' ⊗ₘ k') ≫
      (DayFunctor.η ((represented r).obj M') ((represented s).obj N')).app (r, s))
  simp only [Category.assoc]
  rw [hUnit, ← Category.assoc, hPair, Category.assoc]

/-- The full Day inverse is natural simultaneously in both original coefficient maps. -/
theorem dayInverse_coefficient (r s : SmallFinBijGroupoid)
    {M M' N N' : V} (f : M ⟶ M') (g : N ⟶ N') :
    (represented (r ⊗ s)).map (f ⊗ₘ g) ≫ dayInverse r s M' N' =
      dayInverse r s M N ≫ ((represented r).map f ⊗ₘ (represented s).map g) := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext q
  apply Sigma.hom_ext
  intro h
  let κ : M ⊗ N ⟶ ((represented (r ⊗ s)).obj (M ⊗ N)).functor.obj q :=
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) h
  let κ' : M' ⊗ N' ⟶ ((represented (r ⊗ s)).obj (M' ⊗ N')).functor.obj q :=
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M' ⊗ N') h
  have hκ : κ ≫ ((represented (r ⊗ s)).map (f ⊗ₘ g)).natTrans.app q =
      (f ⊗ₘ g) ≫ κ' := represented_generator_coefficient (r ⊗ s) q (f ⊗ₘ g) h
  have hInv : κ ≫ (dayInverse r s M N).natTrans.app q =
      dayGenerator r s M N ≫
        ((represented r).obj M ⊗ (represented s).obj N).functor.map h :=
    dayInverse_generator r s q M N h
  have hInv' : κ' ≫ (dayInverse r s M' N').natTrans.app q =
      dayGenerator r s M' N' ≫
        ((represented r).obj M' ⊗ (represented s).obj N').functor.map h :=
    dayInverse_generator r s q M' N' h
  have hNat := ((represented r).map f ⊗ₘ (represented s).map g).natTrans.naturality h
  change κ ≫ ((represented (r ⊗ s)).map (f ⊗ₘ g)).natTrans.app q ≫
      (dayInverse r s M' N').natTrans.app q =
    κ ≫ (dayInverse r s M N).natTrans.app q ≫
      ((represented r).map f ⊗ₘ (represented s).map g).natTrans.app q
  have hLeft : κ ≫ ((represented (r ⊗ s)).map (f ⊗ₘ g)).natTrans.app q ≫
      (dayInverse r s M' N').natTrans.app q =
      (f ⊗ₘ g) ≫ dayGenerator r s M' N' ≫
        ((represented r).obj M' ⊗ (represented s).obj N').functor.map h := by
    rw [← Category.assoc, hκ, Category.assoc, hInv']
  have hRight : κ ≫ (dayInverse r s M N).natTrans.app q ≫
      ((represented r).map f ⊗ₘ (represented s).map g).natTrans.app q =
      (f ⊗ₘ g) ≫ dayGenerator r s M' N' ≫
        ((represented r).obj M' ⊗ (represented s).obj N').functor.map h := by
    rw [← Category.assoc, hInv, Category.assoc, hNat,
      ← Category.assoc, dayGenerator_coefficient, Category.assoc]
  exact hLeft.trans hRight.symm

/-- The two actual Day collapses give the complete component comparison. -/
def dayComponentIso (r s q : SmallFinBijGroupoid) (M N : V) :
    ((represented r).obj M ⊗ (represented s).obj N).functor.obj q ≅
      ((represented (r ⊗ s)).obj (M ⊗ N)).functor.obj q :=
  representedTensorComponentIso ((represented r).obj M) s q N ≪≫
    componentIso r s q M N

/-- The composite inverse is the actual identity-generator Day extension
at every original ordered-block bijection. -/
@[reassoc]
theorem dayComponentIso_inv_generator (r s q : SmallFinBijGroupoid) (M N : V)
    (h : r ⊗ s ⟶ q) :
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) h ≫
        (dayComponentIso r s q M N).inv =
      dayGenerator r s M N ≫
        ((represented r).obj M ⊗ (represented s).obj N).functor.map h := by
  let D := diagram r s q M N
  let d := identityDecomposition r s q h
  let T := (represented r).obj M ⊗ (represented s).obj N
  let first : T.functor.obj q ≅ colimit D :=
    representedTensorComponentIso ((represented r).obj M) s q N
  let second : colimit D ≅ ((represented (r ⊗ s)).obj (M ⊗ N)).functor.obj q :=
    componentIso r s q M N
  let κ : M ⊗ N ⟶ ((represented (r ⊗ s)).obj (M ⊗ N)).functor.obj q :=
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) h
  let jR : M ⟶ ((represented r).obj M).functor.obj r :=
    Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r)
  let jS : N ⟶ ((represented s).obj N).functor.obj s :=
    Sigma.ι (fun _ : s ⟶ s => N) (𝟙 s)
  let j : M ⊗ N ⟶ D.obj d := jR ▷ N
  let i : D.obj d ⟶ colimit D := colimit.ι D d
  let w : D.obj d ⟶ ((represented r).obj M).functor.obj r ⊗
      ((represented s).obj N).functor.obj s :=
    ((represented r).obj M).functor.obj r ◁ jS
  let η : ((represented r).obj M).functor.obj r ⊗
      ((represented s).obj N).functor.obj s ⟶ T.functor.obj (r ⊗ s) :=
    (DayFunctor.η ((represented r).obj M) ((represented s).obj N)).app (r, s)
  let τ := T.functor.map h
  have hSecond : κ ≫ second.inv = j ≫ i := backward_generator r s q M N h
  have hFirst : i ≫ first.inv = w ≫ η ≫ τ :=
    representedTensorComponentIso_inv_generator ((represented r).obj M) s q N d
  have hTensor : j ≫ w = jR ⊗ₘ jS := (tensorHom_def jR jS).symm
  change κ ≫ (second.inv ≫ first.inv) = dayGenerator r s M N ≫ τ
  calc
    κ ≫ (second.inv ≫ first.inv) = (κ ≫ second.inv) ≫ first.inv :=
      (Category.assoc _ _ _).symm
    _ = (j ≫ i) ≫ first.inv := congrArg (fun k => k ≫ first.inv) hSecond
    _ = j ≫ (i ≫ first.inv) := Category.assoc _ _ _
    _ = j ≫ w ≫ η ≫ τ := congrArg (fun k => j ≫ k) hFirst
    _ = (jR ⊗ₘ jS) ≫ η ≫ τ := by rw [← Category.assoc, hTensor]
    _ = dayGenerator r s M N ≫ τ := (Category.assoc _ _ _).symm

/-- The original free/evaluation inverse has the same whole component map
as the two actual Day collapses. -/
theorem dayInverse_app (r s q : SmallFinBijGroupoid) (M N : V) :
    (dayInverse r s M N).natTrans.app q = (dayComponentIso r s q M N).inv := by
  apply Sigma.hom_ext
  intro h
  exact (dayInverse_generator r s q M N h).trans
    (dayComponentIso_inv_generator r s q M N h).symm

/-- The full actual Day tensor of the two represented diagrams, natural in
every target bijection, is the represented ordered-block coefficient tensor. -/
def iso (r s : SmallFinBijGroupoid) (M N : V) :
    (represented r).obj M ⊗ (represented s).obj N ≅
      (represented (r ⊗ s)).obj (M ⊗ N) :=
  (DayFunctor.equiv SmallFinBijGroupoid V).inverse.mapIso
    ((NatIso.ofComponents (fun q => (dayComponentIso r s q M N).symm)
      (by
        intro q q' τ
        simpa only [Iso.symm_hom, dayInverse_app] using
          (dayInverse r s M N).natTrans.naturality τ)).symm)

/-- The complete Day forward map is the original two-collapse component map. -/
theorem iso_hom_app (r s q : SmallFinBijGroupoid) (M N : V) :
    (iso r s M N).hom.natTrans.app q = (dayComponentIso r s q M N).hom := rfl

/-- The complete Day inverse is the original free/evaluation adjunct. -/
theorem iso_inv (r s : SmallFinBijGroupoid) (M N : V) :
    (iso r s M N).inv = dayInverse r s M N := by
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext q
  exact (dayInverse_app r s q M N).symm

/-- Every original block label retains the actual free/evaluation generator
in the complete inverse Day comparison. -/
@[reassoc]
theorem iso_inverse_generator (r s q : SmallFinBijGroupoid) (M N : V)
    (h : r ⊗ s ⟶ q) :
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) h ≫
        (iso r s M N).inv.natTrans.app q =
      dayGenerator r s M N ≫
        ((represented r).obj M ⊗ (represented s).obj N).functor.map h := by
  rw [iso_inv]
  exact dayInverse_generator r s q M N h

/-- Simultaneous naturality in both actual coefficient maps of the full Day pair. -/
theorem iso_coefficient (r s : SmallFinBijGroupoid)
    {M M' N N' : V} (f : M ⟶ M') (g : N ⟶ N') :
    ((represented r).map f ⊗ₘ (represented s).map g) ≫ (iso r s M' N').hom =
      (iso r s M N).hom ≫ (represented (r ⊗ s)).map (f ⊗ₘ g) := by
  have h : (represented (r ⊗ s)).map (f ⊗ₘ g) ≫ (iso r s M' N').inv =
      (iso r s M N).inv ≫ ((represented r).map f ⊗ₘ (represented s).map g) := by
    simpa only [iso_inv] using dayInverse_coefficient r s f g
  exact iso_forward_square (V := DayFunctor SmallFinBijGroupoid V)
    (iso r s M N) (iso r s M' N')
    ((represented r).map f ⊗ₘ (represented s).map g)
    ((represented (r ⊗ s)).map (f ⊗ₘ g)) h

/-- The comparison as a natural isomorphism of the two coefficient functors. -/
def bifunctorIso (r s : SmallFinBijGroupoid) :
    (represented r).prod (represented s) ⋙ tensor (DayFunctor SmallFinBijGroupoid V) ≅
      tensor V ⋙ represented (r ⊗ s) :=
  NatIso.ofComponents (fun p => iso r s p.1 p.2) (by
    intro p p' f
    exact iso_coefficient r s f.1 f.2)

/-- The actual source braid relabels the full represented coefficient tensor,
naturally in both coefficient arrows. -/
def sourceOrderBifunctorIso (r s : SmallFinBijGroupoid) :
    tensor V ⋙ represented (r ⊗ s) ≅ tensor V ⋙ represented (s ⊗ r) :=
  NatIso.ofComponents
    (fun p => (DayFunctor.equiv SmallFinBijGroupoid V).inverse.mapIso
      (sourceOrderIso r s p.1 p.2))
    (by
      intro p p' f
      change (DayFunctor.equiv SmallFinBijGroupoid V).inverse.map
          ((evaluationLeftAdjoint V (r ⊗ s)).map (f.1 ⊗ₘ f.2)) ≫
          (DayFunctor.equiv SmallFinBijGroupoid V).inverse.map
            (sourceOrderIso r s p'.1 p'.2).hom =
        (DayFunctor.equiv SmallFinBijGroupoid V).inverse.map
            (sourceOrderIso r s p.1 p.2).hom ≫
          (DayFunctor.equiv SmallFinBijGroupoid V).inverse.map
            ((evaluationLeftAdjoint V (s ⊗ r)).map (f.1 ⊗ₘ f.2))
      simpa only [Functor.map_comp] using
        congrArg ((DayFunctor.equiv SmallFinBijGroupoid V).inverse.map)
          (sourceOrderIso_coefficient r s f.1 f.2))

/-- The complete pair comparison with the original source order `s ⊗ r`. -/
def orderedBifunctorIso (r s : SmallFinBijGroupoid) :
    (represented r).prod (represented s) ⋙ tensor (DayFunctor SmallFinBijGroupoid V) ≅
      tensor V ⋙ represented (s ⊗ r) :=
  bifunctorIso r s ≪≫ sourceOrderBifunctorIso r s

/-- The actual Day pair at two coefficients in the original source order. -/
def orderedIso (r s : SmallFinBijGroupoid) (M N : V) :
    (represented r).obj M ⊗ (represented s).obj N ≅
      (represented (s ⊗ r)).obj (M ⊗ N) :=
  (orderedBifunctorIso r s).app (M, N)

/-- Both coefficient maps are retained by the source-ordered pair comparison. -/
theorem orderedIso_coefficient (r s : SmallFinBijGroupoid)
    {M M' N N' : V} (f : M ⟶ M') (g : N ⟶ N') :
    ((represented r).map f ⊗ₘ (represented s).map g) ≫ (orderedIso r s M' N').hom =
      (orderedIso r s M N).hom ≫ (represented (s ⊗ r)).map (f ⊗ₘ g) :=
  by
    let p : (M, N) ⟶ (M', N') := (f, g)
    exact (orderedBifunctorIso (V := V) r s).hom.naturality p

/-- Every inverse source-ordered label uses the original forward index braid. -/
@[reassoc]
theorem orderedIso_inverse_generator (r s q : SmallFinBijGroupoid) (M N : V)
    (h : s ⊗ r ⟶ q) :
    Sigma.ι (fun _ : s ⊗ r ⟶ q => M ⊗ N) h ≫
        (orderedIso r s M N).inv.natTrans.app q =
      dayGenerator r s M N ≫
        ((represented r).obj M ⊗ (represented s).obj N).functor.map ((β_ r s).hom ≫ h) := by
  let κ : M ⊗ N ⟶ ((represented (s ⊗ r)).obj (M ⊗ N)).functor.obj q :=
    Sigma.ι (fun _ : s ⊗ r ⟶ q => M ⊗ N) h
  let κ' : M ⊗ N ⟶ ((represented (r ⊗ s)).obj (M ⊗ N)).functor.obj q :=
    Sigma.ι (fun _ : r ⊗ s ⟶ q => M ⊗ N) ((β_ r s).hom ≫ h)
  let t : ((represented (s ⊗ r)).obj (M ⊗ N)).functor.obj q ⟶
      ((represented (r ⊗ s)).obj (M ⊗ N)).functor.obj q :=
    (sourceOrderIso r s M N).inv.app q
  have hIndex : κ ≫ t = κ' :=
    indexMap_generator (β_ r s).hom (M ⊗ N) q h
  change κ ≫ (t ≫
    (iso r s M N).inv.natTrans.app q) = _
  rw [← Category.assoc, hIndex]
  exact iso_inverse_generator r s q M N ((β_ r s).hom ≫ h)

end DayComparison

end CategoryTheory.Operad.SmallFinBijGroupoid.RepresentablePair
