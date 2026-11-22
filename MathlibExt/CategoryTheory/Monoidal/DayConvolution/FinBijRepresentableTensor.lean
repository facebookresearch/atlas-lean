/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FinBijDecomposition

/-!
# Day tensor components with a finite-bijection representable

The right factor is the actual coproduct-valued free diagram. The coefficient
is any Day functor. Both comparison maps use the original Day Kan extension
and complement-first decomposition cocones from `FinBijDecomposition`.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory
open scoped ExternalProduct

namespace CategoryTheory.Operad.SmallFinBijGroupoid

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The original ordinary free diagram, with its unchanged Day wrapper. -/
def representedDiagram (i : SmallFinBijGroupoid) : V ⥤ DayFunctor SmallFinBijGroupoid V :=
  evaluationLeftAdjoint V i ⋙ (DayFunctor.equiv SmallFinBijGroupoid V).inverse

/-- The original coproduct generator at the identity input label. -/
def representedGenerator (i : SmallFinBijGroupoid) (X : V) :
    X ⟶ ((representedDiagram i).obj X).functor.obj i :=
  Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i)

/-- The actual Day extension's entire complement-first labeled generator. -/
def representedTensorGenerator (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) (X : V) (d : BlockDecomposition i m) :
    A.functor.obj d.left ⊗ X ⟶ (A ⊗ (representedDiagram i).obj X).functor.obj m :=
  (A.functor.obj d.left ◁ representedGenerator i X) ≫
    (DayFunctor.η A ((representedDiagram i).obj X)).app (d.left, i) ≫
      (A ⊗ (representedDiagram i).obj X).functor.map d.hom

/-- The complete Day tensor component is the original decomposition colimit,
without a monoid structure on the coefficient functor. -/
def representedTensorComponentIso (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) (X : V) :
    (A ⊗ (representedDiagram i).obj X).functor.obj m ≅
      (dayFreeAtComponentFunctor A i m).obj X := by
  let G := (representedDiagram i).obj X
  let D := CostructuredArrow.proj (tensor SmallFinBijGroupoid) m ⋙ (A.functor ⊠ G.functor)
  let B := CostructuredArrow.proj (tensorRight i) m ⋙ A.functor ⋙ tensorRight X
  let hDay : (Functor.LeftExtension.mk (A ⊗ G).functor
      (DayFunctor.η A G)).IsPointwiseLeftKanExtensionAt m :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      (C := SmallFinBijGroupoid) (V := V) (D := DayFunctor SmallFinBijGroupoid V) A G m
  let k : colimit D ≅ colimit B :=
    { hom := colimit.desc D (dayTensorCollapseCocone A i m X)
      inv := colimit.desc B (dayFreeAtComponentBackward A i m X)
      hom_inv_id := dayFreeAtComponentForward_backward A i m X
      inv_hom_id := dayFreeAtComponentBackward_forward A i m X }
  exact hDay.isoColimit ≪≫ k

/-- Every inverse comparison leg is the actual free-diagram generator followed
by the original labeled Day extension map. -/
@[reassoc]
theorem representedTensorComponentIso_inv_generator (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) (X : V) (d : BlockDecomposition i m) :
    colimit.ι (CostructuredArrow.proj (tensorRight i) m ⋙ A.functor ⋙ tensorRight X) d ≫
        (representedTensorComponentIso A i m X).inv =
      representedTensorGenerator A i m X d := by
  let G := (representedDiagram i).obj X
  let D := CostructuredArrow.proj (tensor SmallFinBijGroupoid) m ⋙ (A.functor ⊠ G.functor)
  let B := CostructuredArrow.proj (tensorRight i) m ⋙ A.functor ⋙ tensorRight X
  let q : CostructuredArrow (tensor SmallFinBijGroupoid) m :=
    CostructuredArrow.mk (Y := (d.left, i)) d.hom
  let hDay : (Functor.LeftExtension.mk (A ⊗ G).functor
      (DayFunctor.η A G)).IsPointwiseLeftKanExtensionAt m :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      (C := SmallFinBijGroupoid) (V := V) (D := DayFunctor SmallFinBijGroupoid V) A G m
  have h := congrArg (fun t => t ≫ hDay.isoColimit.inv) (hDay.ι_isoColimit_hom q)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  let k : colimit B ⟶ colimit D :=
    colimit.desc B (dayFreeAtComponentBackward A i m X)
  let j : A.functor.obj d.left ⊗ X ⟶ D.obj q :=
    𝟙 (A.functor.obj d.left) ⊗ₘ representedGenerator i X
  let ν := (DayFunctor.η A G).app (d.left, i) ≫ (A ⊗ G).functor.map d.hom
  have hν : colimit.ι D q ≫ hDay.isoColimit.inv = ν := h.symm
  have hk : colimit.ι B d ≫ k = j ≫ colimit.ι D q :=
    colimit.ι_desc (dayFreeAtComponentBackward A i m X) d
  have hpre : (colimit.ι B d ≫ k) ≫ hDay.isoColimit.inv =
      (j ≫ colimit.ι D q) ≫ hDay.isoColimit.inv :=
    congrArg (fun f => f ≫ hDay.isoColimit.inv) hk
  have hj : (j ≫ colimit.ι D q) ≫ hDay.isoColimit.inv = j ≫ ν :=
    (Category.assoc j (colimit.ι D q) hDay.isoColimit.inv).trans
      (congrArg (fun f => j ≫ f) hν)
  have hgen : j ≫ ν = representedTensorGenerator A i m X d :=
    congrArg (fun f => f ≫ ν) (id_tensorHom (A.functor.obj d.left)
      (representedGenerator i X))
  change colimit.ι B d ≫ (k ≫ hDay.isoColimit.inv) = _
  exact (Category.assoc (colimit.ι B d) k hDay.isoColimit.inv).symm.trans
    (hpre.trans (hj.trans hgen))

/-- The complete forward comparison returns the original decomposition leg. -/
@[reassoc]
theorem representedTensorComponentIso_generator (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) (X : V) (d : BlockDecomposition i m) :
    representedTensorGenerator A i m X d ≫ (representedTensorComponentIso A i m X).hom =
      colimit.ι (CostructuredArrow.proj (tensorRight i) m ⋙ A.functor ⋙ tensorRight X) d := by
  let e := representedTensorComponentIso A i m X
  let q : A.functor.obj d.left ⊗ X ⟶ (dayFreeAtComponentFunctor A i m).obj X :=
    colimit.ι (CostructuredArrow.proj (tensorRight i) m ⋙ A.functor ⋙ tensorRight X) d
  have h : q ≫ e.inv = representedTensorGenerator A i m X d :=
    representedTensorComponentIso_inv_generator A i m X d
  have hc : (q ≫ e.inv) ≫ e.hom = q :=
    (Category.assoc q e.inv e.hom).trans
      ((congrArg (fun f => q ≫ f) e.inv_hom_id).trans (Category.comp_id q))
  exact (congrArg (fun f => f ≫ e.hom) h).symm.trans hc


open LawfulDayConvolutionMonoidalCategoryStruct

omit [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The actual represented diagram retains every coefficient arrow at its
original identity coproduct leg. -/
theorem representedGenerator_naturality (i : SmallFinBijGroupoid) {X Y : V} (f : X ⟶ Y) :
    representedGenerator i X ≫ ((representedDiagram i).map f).natTrans.app i =
      f ≫ representedGenerator i Y := by
  change Sigma.ι (fun _ : i ⟶ i => X) (𝟙 i) ≫
      (Sigma.desc (fun h : i ⟶ i => f ≫ Sigma.ι (fun _ : i ⟶ i => Y) h)) = _
  exact Sigma.ι_comp_desc _ _

/-- The complete evaluated Day tensor is functorial in the represented
coefficient object by its actual original Day tensor map. -/
def representedTensorComponentFunctor (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) : V ⥤ V :=
  representedDiagram i ⋙ tensorLeft A ⋙ (DayFunctor.equiv SmallFinBijGroupoid V).functor ⋙
    (evaluation SmallFinBijGroupoid V).obj m

/-- The entire coefficient map is the actual Day left-tensor map at the
unchanged output label. -/
theorem representedTensorComponentFunctor_map (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) {X Y : V} (f : X ⟶ Y) :
    (representedTensorComponentFunctor A i m).map f =
      (A ◁ (representedDiagram i).map f).natTrans.app m := rfl

/-- Every labeled generator respects the whole original coefficient map. -/
theorem representedTensorGenerator_naturality (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) {X Y : V} (f : X ⟶ Y) (d : BlockDecomposition i m) :
    (A.functor.obj d.left ◁ f) ≫ representedTensorGenerator A i m Y d =
      representedTensorGenerator A i m X d ≫
        (representedTensorComponentFunctor A i m).map f := by
  let GX := (representedDiagram i).obj X
  let GY := (representedDiagram i).obj Y
  let g : GX ⟶ GY := (representedDiagram i).map f
  let a := A.functor.obj d.left
  let eX := (DayFunctor.η A GX).app (d.left, i)
  let eY := (DayFunctor.η A GY).app (d.left, i)
  let tX := (A ⊗ GX).functor.map d.hom
  let tY := (A ⊗ GY).functor.map d.hom
  let b := (A ◁ g).natTrans.app (d.left ⊗ i)
  let k := (A ◁ g).natTrans.app m
  have hη : eX ≫ b = (a ◁ g.natTrans.app i) ≫ eY :=
    convolutionExtensionUnit_comp_ι_map_whiskerLeft_app V A g d.left i
  have ht : tX ≫ k = b ≫ tY := (A ◁ g).natTrans.naturality d.hom
  have hg : representedGenerator i X ≫ g.natTrans.app i =
      f ≫ representedGenerator i Y := representedGenerator_naturality i f
  rw [representedTensorComponentFunctor_map]
  change (a ◁ f) ≫ ((a ◁ representedGenerator i Y) ≫ eY ≫ tY) =
    ((a ◁ representedGenerator i X) ≫ eX ≫ tX) ≫ k
  symm
  calc
    _ = (a ◁ representedGenerator i X) ≫ eX ≫ (tX ≫ k) := by
      simp only [Category.assoc]
    _ = (a ◁ representedGenerator i X) ≫ (eX ≫ b) ≫ tY := by
      rw [ht]
      simp only [Category.assoc]
    _ = (a ◁ representedGenerator i X) ≫ (a ◁ g.natTrans.app i) ≫ eY ≫ tY := by
      rw [hη]
      simp only [Category.assoc]
    _ = (a ◁ (representedGenerator i X ≫ g.natTrans.app i)) ≫ eY ≫ tY := by
      rw [whiskerLeft_comp]
      simp only [Category.assoc]
    _ = (a ◁ (f ≫ representedGenerator i Y)) ≫ eY ≫ tY := by rw [hg]
    _ = _ := by
      rw [whiskerLeft_comp]
      simp only [Category.assoc]

/-- Both actual inverse component maps retain every original coefficient
arrow, before choosing complement or orbit representatives. -/
theorem representedTensorComponentIso_inv_naturality (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) {X Y : V} (f : X ⟶ Y) :
    (dayFreeAtComponentFunctor A i m).map f ≫ (representedTensorComponentIso A i m Y).inv =
      (representedTensorComponentIso A i m X).inv ≫
        (representedTensorComponentFunctor A i m).map f := by
  let BX := CostructuredArrow.proj (tensorRight i) m ⋙ A.functor ⋙ tensorRight X
  let BY := CostructuredArrow.proj (tensorRight i) m ⋙ A.functor ⋙ tensorRight Y
  let bmap : BX ⟶ BY :=
    { app := fun d => 𝟙 (A.functor.obj d.left) ⊗ₘ f
      naturality := by
        intro d e h
        change (A.functor.map h.left ▷ X) ≫ (𝟙 (A.functor.obj e.left) ⊗ₘ f) =
          (𝟙 (A.functor.obj d.left) ⊗ₘ f) ≫ (A.functor.map h.left ▷ Y)
        simpa only [id_tensorHom] using
          (whisker_exchange (A.functor.map h.left) f).symm }
  let _ : HasColimitsOfShape (BlockDecomposition i m) V :=
    HasColimitsOfSize.has_colimits_of_shape (BlockDecomposition i m)
  let L : (BlockDecomposition i m ⥤ V) ⥤ V := colim
  have hb : (dayFreeAtComponentFunctor A i m).map f = L.map bmap := rfl
  rw [hb]
  change L.map bmap ≫ (representedTensorComponentIso A i m Y).inv =
    (representedTensorComponentIso A i m X).inv ≫
      (representedTensorComponentFunctor A i m).map f
  apply colimit.hom_ext
  intro d
  have hmap := congrArg (fun t => t ≫ (representedTensorComponentIso A i m Y).inv)
    (ι_colimMap bmap d)
  have hy := representedTensorComponentIso_inv_generator A i m Y d
  have hx := representedTensorComponentIso_inv_generator A i m X d
  have hn := representedTensorGenerator_naturality A i m f d
  change (colimit.ι BX d ≫ colim.{0, 0, v, u}.map bmap) ≫
      (representedTensorComponentIso A i m Y).inv = _ at hmap
  change _ = ((𝟙 (A.functor.obj d.left) ⊗ₘ f) ≫ colimit.ι BY d) ≫
    (representedTensorComponentIso A i m Y).inv at hmap
  rw [id_tensorHom] at hmap
  let eX := (representedTensorComponentIso A i m X).inv
  let eY := (representedTensorComponentIso A i m Y).inv
  let qX : A.functor.obj d.left ⊗ X ⟶ (dayFreeAtComponentFunctor A i m).obj X :=
    colimit.ι BX d
  let qY : A.functor.obj d.left ⊗ Y ⟶ (dayFreeAtComponentFunctor A i m).obj Y :=
    colimit.ι BY d
  let a := A.functor.obj d.left ◁ f
  let k := (representedTensorComponentFunctor A i m).map f
  have h1 : qX ≫ L.map bmap ≫ eY = a ≫ qY ≫ eY :=
    (Category.assoc qX (L.map bmap) eY).symm.trans
      (hmap.trans (Category.assoc a qY eY))
  have h2 : a ≫ qY ≫ eY = a ≫ representedTensorGenerator A i m Y d :=
    congrArg (fun t => a ≫ t) hy
  have h3 : representedTensorGenerator A i m X d ≫ k = qX ≫ eX ≫ k :=
    (congrArg (fun t => t ≫ k) hx).symm.trans (Category.assoc qX eX k)
  exact h1.trans (h2.trans (hn.trans h3))

/-- The full Day representable tensor comparison is natural in every
coefficient arrow, using its actual two inverse maps. -/
def representedTensorNatIso (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) :
    representedTensorComponentFunctor A i m ≅ dayFreeAtComponentFunctor A i m :=
  (NatIso.ofComponents (fun X => (representedTensorComponentIso A i m X).symm)
    (by
      intro X Y f
      exact representedTensorComponentIso_inv_naturality A i m f)).symm

/-- The complete forward natural isomorphism uses the same original
component comparison maps. -/
theorem representedTensorNatIso_hom_app (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) (X : V) :
    (representedTensorNatIso A i m).hom.app X =
      (representedTensorComponentIso A i m X).hom := rfl

/-- The inverse natural isomorphism retains the original coproduct
generator followed by the whole labeled Day extension. -/
theorem representedTensorNatIso_inv_app (A : DayFunctor SmallFinBijGroupoid V)
    (i m : SmallFinBijGroupoid) (X : V) :
    (representedTensorNatIso A i m).inv.app X =
      (representedTensorComponentIso A i m X).inv := rfl

/-- Every cardinal component of the actual tensor has the full original
complement-action orbit description, naturally in the coefficient. -/
def representedTensorCardInducedIso (A : DayFunctor SmallFinBijGroupoid V)
    {n m : ℕ} (h : n ≤ m) :
    representedTensorComponentFunctor A (card n) (card m) ≅ cardInducedFunctor A n m h :=
  representedTensorNatIso A (card n) (card m) ≪≫ Mod.cardComponentInducedIso A h


/-- An arbitrary Day coefficient map acts on the entire complement
decomposition diagram at every original finite label. -/
def representedDecompositionMap {A A' : DayFunctor SmallFinBijGroupoid V} (f : A ⟶ A')
    (i m : SmallFinBijGroupoid) (X : V) :
    (CostructuredArrow.proj (tensorRight i) m ⋙ A.functor ⋙ tensorRight X) ⟶
      (CostructuredArrow.proj (tensorRight i) m ⋙ A'.functor ⋙ tensorRight X) where
  app d := f.natTrans.app d.left ▷ X
  naturality d e h := by
    change (A.functor.map h.left ▷ X) ≫ (f.natTrans.app e.left ▷ X) =
      (f.natTrans.app d.left ▷ X) ≫ (A'.functor.map h.left ▷ X)
    have hf := f.natTrans.naturality h.left
    simpa only [comp_whiskerRight] using congrArg (fun t => t ▷ X) hf

/-- The original coefficient map on the full Day tensor retains every
represented scalar and original output label. -/
def representedTensorCoefficientMap {A A' : DayFunctor SmallFinBijGroupoid V} (f : A ⟶ A')
    (i m : SmallFinBijGroupoid) (X : V) :
    (A ⊗ (representedDiagram i).obj X).functor.obj m ⟶
      (A' ⊗ (representedDiagram i).obj X).functor.obj m :=
  (f ▷ (representedDiagram i).obj X).natTrans.app m

/-- Every original Day coefficient arrow respects the complete labeled
generator before either complement or orbit normalization. -/
theorem representedTensorGenerator_coefficient {A A' : DayFunctor SmallFinBijGroupoid V}
    (f : A ⟶ A') (i m : SmallFinBijGroupoid) (X : V) (d : BlockDecomposition i m) :
    (f.natTrans.app d.left ▷ X) ≫ representedTensorGenerator A' i m X d =
      representedTensorGenerator A i m X d ≫ representedTensorCoefficientMap f i m X := by
  let G := (representedDiagram i).obj X
  let g := f ▷ G
  let e := (DayFunctor.η A G).app (d.left, i)
  let e' := (DayFunctor.η A' G).app (d.left, i)
  let t := (A ⊗ G).functor.map d.hom
  let t' := (A' ⊗ G).functor.map d.hom
  let b := g.natTrans.app (d.left ⊗ i)
  let k := g.natTrans.app m
  have hη : e ≫ b = (f.natTrans.app d.left ▷ G.functor.obj i) ≫ e' :=
    convolutionExtensionUnit_comp_ι_map_whiskerRight_app SmallFinBijGroupoid V f G d.left i
  have ht : t ≫ k = b ≫ t' := g.natTrans.naturality d.hom
  have hex : (A.functor.obj d.left ◁ representedGenerator i X) ≫
      (f.natTrans.app d.left ▷ G.functor.obj i) =
    (f.natTrans.app d.left ▷ X) ≫ (A'.functor.obj d.left ◁ representedGenerator i X) :=
    whisker_exchange (f.natTrans.app d.left) (representedGenerator i X)
  change (f.natTrans.app d.left ▷ X) ≫
      ((A'.functor.obj d.left ◁ representedGenerator i X) ≫ e' ≫ t') =
    ((A.functor.obj d.left ◁ representedGenerator i X) ≫ e ≫ t) ≫ k
  symm
  calc
    _ = (A.functor.obj d.left ◁ representedGenerator i X) ≫ e ≫ (t ≫ k) := by
      simp only [Category.assoc]
    _ = (A.functor.obj d.left ◁ representedGenerator i X) ≫ (e ≫ b) ≫ t' := by
      rw [ht]
      simp only [Category.assoc]
    _ = (A.functor.obj d.left ◁ representedGenerator i X) ≫
        (f.natTrans.app d.left ▷ G.functor.obj i) ≫ e' ≫ t' := by
      rw [hη]
      simp only [Category.assoc]
    _ = _ := by
      rw [← Category.assoc, ← Category.assoc, hex]
      simp only [Category.assoc]

/-- The inverse of the actual component comparison respects every whole
Day coefficient map, including maps not induced by a represented scalar. -/
theorem representedTensorComponentIso_inv_coefficient
    {A A' : DayFunctor SmallFinBijGroupoid V} (f : A ⟶ A')
    (i m : SmallFinBijGroupoid) (X : V) :
    colim.{0, 0, v, u}.map (representedDecompositionMap f i m X) ≫
        (representedTensorComponentIso A' i m X).inv =
      (representedTensorComponentIso A i m X).inv ≫
        representedTensorCoefficientMap f i m X := by
  let B := CostructuredArrow.proj (tensorRight i) m ⋙ A.functor ⋙ tensorRight X
  let B' := CostructuredArrow.proj (tensorRight i) m ⋙ A'.functor ⋙ tensorRight X
  let L : (BlockDecomposition i m ⥤ V) ⥤ V := colim.{0, 0, v, u}
  apply colimit.hom_ext
  intro d
  have hmap := congrArg (fun t => t ≫ (representedTensorComponentIso A' i m X).inv)
    (ι_colimMap (representedDecompositionMap f i m X) d)
  change (colimit.ι B d ≫ L.map (representedDecompositionMap f i m X)) ≫
      (representedTensorComponentIso A' i m X).inv =
    ((f.natTrans.app d.left ▷ X) ≫ colimit.ι B' d) ≫
      (representedTensorComponentIso A' i m X).inv at hmap
  have h' := representedTensorComponentIso_inv_generator A' i m X d
  have h := representedTensorComponentIso_inv_generator A i m X d
  have hn := representedTensorGenerator_coefficient f i m X d
  calc
    _ = (colimit.ι B d ≫ L.map (representedDecompositionMap f i m X)) ≫
        (representedTensorComponentIso A' i m X).inv :=
      (Category.assoc (colimit.ι B d) (L.map (representedDecompositionMap f i m X))
        (representedTensorComponentIso A' i m X).inv).symm
    _ = ((f.natTrans.app d.left ▷ X) ≫ colimit.ι B' d) ≫
        (representedTensorComponentIso A' i m X).inv := hmap
    _ = (f.natTrans.app d.left ▷ X) ≫
        (colimit.ι B' d ≫ (representedTensorComponentIso A' i m X).inv) :=
      Category.assoc (f.natTrans.app d.left ▷ X) (colimit.ι B' d)
        (representedTensorComponentIso A' i m X).inv
    _ = (f.natTrans.app d.left ▷ X) ≫ representedTensorGenerator A' i m X d := by rw [h']
    _ = representedTensorGenerator A i m X d ≫
        representedTensorCoefficientMap f i m X := hn
    _ = _ := by
      exact (congrArg (fun t => t ≫ representedTensorCoefficientMap f i m X) h).symm.trans
        (Category.assoc (colimit.ι B d) (representedTensorComponentIso A i m X).inv
          (representedTensorCoefficientMap f i m X))

private theorem iso_hom_square {D : Type*} [Category D] {X Y X' Y' : D}
    (e : X ≅ Y) (e' : X' ≅ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : g ≫ e'.inv = e.inv ≫ f) : f ≫ e'.hom = e.hom ≫ g := by
  apply (cancel_epi e.inv).1
  rw [← Category.assoc, ← h, Category.assoc, e'.inv_hom_id, Category.comp_id,
    ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- The forward comparison keeps the same complete Day coefficient
map on both sides of the actual decomposition colimit. -/
theorem representedTensorComponentIso_coefficient
    {A A' : DayFunctor SmallFinBijGroupoid V} (f : A ⟶ A')
    (i m : SmallFinBijGroupoid) (X : V) :
    representedTensorCoefficientMap f i m X ≫ (representedTensorComponentIso A' i m X).hom =
      (representedTensorComponentIso A i m X).hom ≫
        colim.{0, 0, v, u}.map (representedDecompositionMap f i m X) :=
  iso_hom_square (representedTensorComponentIso A i m X)
    (representedTensorComponentIso A' i m X)
    (representedTensorCoefficientMap f i m X)
    (colim.{0, 0, v, u}.map (representedDecompositionMap f i m X))
    (representedTensorComponentIso_inv_coefficient f i m X)



/-- A genuine finite-bijection decomposition cannot have a larger
represented block than its output cardinality. -/
theorem representedBlock_le {n m : ℕ} (d : BlockDecomposition (card n) (card m)) : n ≤ m := by
  have hObj : (d.left ⊗ card n).of = (card m).of :=
    FintypeCat.Skeleton.is_skeletal ⟨d.hom.iso⟩
  have hLen := congrArg FintypeCat.Skeleton.len hObj
  change d.left.of.len + n = m at hLen
  rw [← hLen]
  exact Nat.le_add_left n d.left.of.len

/-- Below the represented degree, the full actual Day tensor component
is initial for every coefficient functor. -/
def representedTensorBelowIsInitial (A : DayFunctor SmallFinBijGroupoid V)
    {n m : ℕ} (h : m < n) (X : V) :
    IsInitial ((representedTensorComponentFunctor A (card n) (card m)).obj X) := by
  letI : IsEmpty (BlockDecomposition (card n) (card m)) :=
    ⟨fun d => (Nat.not_le_of_gt h) (representedBlock_le d)⟩
  let B := CostructuredArrow.proj (tensorRight (card n)) (card m) ⋙ A.functor ⋙ tensorRight X
  let hi : IsInitial (colimit B) :=
    isColimitEquivIsInitialOfIsEmpty V (colimit.cocone B) (colimit.isColimit B)
  exact hi.ofIso (representedTensorComponentIso A (card n) (card m) X).symm

end CategoryTheory.Operad.SmallFinBijGroupoid
