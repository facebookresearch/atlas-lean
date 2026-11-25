/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Historical terminal-weight proofs: @toskua, Avocado; shared by the canonical
-- universe-general core.

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentation
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataEvaluation
import MathlibExt.AlgebraicTopology.SimplicialObject.DataIso
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Actual terminal-weight rows with independent original scalar universe

Fixing an inner simplicial degree in the terminal-weight ordinary weighted bar
gives the ordinary simplicial replacement of the evaluated coefficient
functor.  Degreewise, evaluation first commutes with the functor-category
coproduct, and then the terminal `PUnit` weight is reassociated from the
weighted index into the right coefficient of the category bar.

This is the single universe-general implementation of the original
@toskua/Avocado terminal-weight proof at `SSet.{max uJ vJ w}`. It retains
independent index object, index Hom and additional scalar universes. The
historical inferable API is an explicit scalar-universe-zero specialization
in `BousfieldKanTerminalWeightRows`, sharing these exact maps and proofs.

The comparison below proves every face and degeneracy square, and identifies
the evaluated weighted-bar augmentation on each summand.  It makes no
diagonal, realization, weak-equivalence, or Theorem A claim.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

universe uJ vJ w

namespace SSet.BousfieldKanRowsOf

variable {J : Type uJ} [Category.{vJ} J]

/-- Evaluation of an `SSet`-valued diagram in one inner simplicial degree.
For the simplex-pullback diagram this is definitionally the coefficient
functor named `simplexPullbackDegree` in the BK3a layer. -/
abbrev wbarDegreeCoefficient (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) : J ⥤ Type (max uJ vJ w) :=
  D ⋙ (evaluation SimplexCategoryᵒᵖ (Type (max uJ vJ w))).obj a

@[simp]
theorem wbarDegreeCoefficient_obj (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) (j : J) :
    (wbarDegreeCoefficient D a).obj j = (D.obj j).obj a :=
  rfl

@[simp]
theorem wbarDegreeCoefficient_map_apply (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) {j k : J} (f : j ⟶ k)
    (x : (D.obj j).obj a) :
    (wbarDegreeCoefficient D a).map f x = (D.map f).app a x :=
  rfl

/-- Simplicial data obtained by evaluating every weighted-bar coefficient in
the fixed inner degree `a`. -/
noncomputable abbrev wbarRowData (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) : SimplicialObject.Data (Type (max uJ vJ w)) :=
  SimplicialObject.Data.evalObj a
    (StrictOrdinaryWeightedBar.wbarData (CategoryBar.replUnit J) D)

/-- The fixed-inner-degree row of the terminal-weight weighted bar. -/
noncomputable abbrev wbarRow (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) : SSet.{max uJ vJ w} :=
  (wbarRowData D a).toSimplicialObject

/-- Canonical comparison between evaluating the promoted weighted bar and
promoting its evaluated data. -/
noncomputable def wbarRowEvaluationIso (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) :
    (StrictOrdinaryWeightedBar.wbarData
          (CategoryBar.replUnit J) D).toSimplicialObject ⋙
        (evaluation SimplexCategoryᵒᵖ (Type (max uJ vJ w))).obj a ≅
      wbarRow D a :=
  SimplicialObject.Data.evalToSimplicialIso
    (StrictOrdinaryWeightedBar.wbarData (CategoryBar.replUnit J) D) a

@[simp]
theorem wbarRowEvaluationIso_hom_app (D : J ⥤ SSet.{max uJ vJ w})
    (a b : SimplexCategoryᵒᵖ) :
    (wbarRowEvaluationIso D a).hom.app b = 𝟙 _ :=
  SimplicialObject.Data.evalToSimplicialIso_hom_app _ _ _

@[simp]
theorem wbarRowEvaluationIso_inv_app (D : J ⥤ SSet.{max uJ vJ w})
    (a b : SimplexCategoryᵒᵖ) :
    (wbarRowEvaluationIso D a).inv.app b = 𝟙 _ :=
  SimplicialObject.Data.evalToSimplicialIso_inv_app _ _ _

@[simp]
theorem wbarRowData_obj (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (wbarRowData D a).obj n =
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit J) D n).obj a :=
  rfl

@[simp]
theorem wbarRow_obj_mk (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (wbarRow D a).obj (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit J) D n).obj a :=
  rfl

@[simp]
theorem wbarRow_map_δ (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) {n : ℕ} (i : Fin (n + 2)) :
    (wbarRow D a).map (SimplexCategory.δ i).op =
      (StrictOrdinaryWeightedBar.wbarδ
        (CategoryBar.replUnit J) D n i).app a := by
  exact SimplicialObject.Data.toSimplicialObject_map_δ _ i

@[simp]
theorem wbarRow_map_σ (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) {n : ℕ} (i : Fin (n + 1)) :
    (wbarRow D a).map (SimplexCategory.σ i).op =
      (StrictOrdinaryWeightedBar.wbarσ
        (CategoryBar.replUnit J) D n i).app a := by
  exact SimplicialObject.Data.toSimplicialObject_map_σ _ i

/-- Reassociation which moves the terminal weight out of the weighted index
and into the right coefficient of the ordinary category bar. -/
def terminalWeightSigmaEquiv (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (Σ p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n,
      (D.obj p.1.left).obj a) ≃
      CategoryBar.replObj J (wbarDegreeCoefficient D a) n where
  toFun
    | ⟨⟨s, w⟩, x⟩ => ⟨s, x, w⟩
  invFun
    | ⟨s, x, w⟩ => ⟨⟨s, w⟩, x⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem terminalWeightSigmaEquiv_apply (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) {n : ℕ}
    (s : ComposableArrows J n) (w : PUnit) (x : (D.obj s.left).obj a) :
    terminalWeightSigmaEquiv D a n ⟨⟨s, w⟩, x⟩ =
      (⟨s, x, w⟩ : CategoryBar.replObj J
        (wbarDegreeCoefficient D a) n) :=
  rfl

@[simp]
theorem terminalWeightSigmaEquiv_symm_apply (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) {n : ℕ}
    (s : ComposableArrows J n) (w : PUnit) (x : (D.obj s.left).obj a) :
    (terminalWeightSigmaEquiv D a n).symm
        (⟨s, x, w⟩ : CategoryBar.replObj J
          (wbarDegreeCoefficient D a) n) =
      ⟨⟨s, w⟩, x⟩ :=
  rfl

/-- Inclusion of one evaluated coefficient in the ordinary simplicial-
replacement degree, retaining the chain and terminal weight. -/
def terminalWeightReplIncl (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (D.obj p.1.left).obj a ⟶
      (CategoryBar.simplicialReplacementData
        (wbarDegreeCoefficient D a)).obj n :=
  ↾fun x => ⟨p.1, x, p.2⟩

@[simp↓]
theorem terminalWeightReplIncl_apply (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj a) :
    terminalWeightReplIncl D a n p x =
      (⟨p.1, x, p.2⟩ : CategoryBar.replObj J
        (wbarDegreeCoefficient D a) n) :=
  rfl

/-- Inclusion of one evaluated coefficient into a weighted-bar row.  It is
the explicit evaluated coproduct inclusion followed by the inverse
`sigmaObjIso`. -/
@[no_expose]
noncomputable def wbarRowIncl (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (D.obj p.1.left).obj a ⟶ (wbarRowData D a).obj n :=
  Limits.Sigma.ι
      (fun p : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) n => (D.obj p.1.left).obj a) p ≫
    (Limits.sigmaObjIso
      (fun p : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) n => D.obj p.1.left) a).inv

/-- The explicit row inclusion is the evaluation of `wbarIncl`. -/
theorem wbarRowIncl_eq_wbarIncl_app (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    wbarRowIncl D a n p =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app a :=
  Limits.ι_comp_sigmaObjIso_inv _ _ _

/-- Degreewise terminal-weight comparison. -/
@[no_expose]
noncomputable def terminalWeightRowDegreeIso (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (wbarRowData D a).obj n ≅
      (CategoryBar.simplicialReplacementData
        (wbarDegreeCoefficient D a)).obj n :=
  Limits.sigmaObjIso
      (fun p : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n => D.obj p.1.left) a ≪≫
    Limits.Types.coproductIso
      (fun p : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n => (D.obj p.1.left).obj a) ≪≫
    (terminalWeightSigmaEquiv D a n).toIso

/-- Computation of the degree comparison on the explicit evaluated row
inclusion. -/
@[reassoc]
theorem terminalWeightRowDegreeIso_hom_rowIncl
    (D : J ⥤ SSet.{max uJ vJ w}) (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    wbarRowIncl D a n p ≫ (terminalWeightRowDegreeIso D a n).hom =
      terminalWeightReplIncl D a n p := by
  change
    (Limits.Sigma.ι
        (fun p : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n => (D.obj p.1.left).obj a) p ≫
      (Limits.sigmaObjIso
        (fun p : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n => D.obj p.1.left) a).inv) ≫
      ((Limits.sigmaObjIso
          (fun p : StrictOrdinaryWeightedBar.WIdx J
            (CategoryBar.replUnit J) n => D.obj p.1.left) a).hom ≫
        (Limits.Types.coproductIso
          (fun p : StrictOrdinaryWeightedBar.WIdx J
            (CategoryBar.replUnit J) n => (D.obj p.1.left).obj a)).hom ≫
        (terminalWeightSigmaEquiv D a n).toIso.hom) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc,
    ← Category.assoc, Limits.Types.coproductIso_ι_comp_hom]
  rfl

/-- A weighted summand is sent to the same chain and coefficient, with its
terminal weight moved to the category-bar right coefficient. -/
@[reassoc]
theorem terminalWeightRowDegreeIso_hom_ι
    (D : J ⥤ SSet.{max uJ vJ w}) (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app a ≫
      (terminalWeightRowDegreeIso D a n).hom =
      terminalWeightReplIncl D a n p := by
  rw [← wbarRowIncl_eq_wbarIncl_app D a n p]
  exact terminalWeightRowDegreeIso_hom_rowIncl D a n p

@[simp↓]
theorem terminalWeightRowDegreeIso_hom_ι_apply
    (D : J ⥤ SSet.{max uJ vJ w}) (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj a) :
    (terminalWeightRowDegreeIso D a n).hom
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app a x) =
      (⟨p.1, x, p.2⟩ : CategoryBar.replObj J
        (wbarDegreeCoefficient D a) n) := by
  exact ConcreteCategory.congr_hom
    (terminalWeightRowDegreeIso_hom_ι D a n p) x

/-- The complete original weighted coefficient inclusions determine every actual original
row map. -/
theorem wbarRow_hom_ext (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) (n : ℕ) {P : Type (max uJ vJ w)}
    {f g : (wbarRowData D a).obj n ⟶ P}
    (h : ∀ p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n,
      wbarRowIncl D a n p ≫ f = wbarRowIncl D a n p ≫ g) :
    f = g := by
  let e := Limits.sigmaObjIso
    (fun p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n => D.obj p.1.left) a
  change
    ((∐ fun p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n => D.obj p.1.left).obj a ⟶ P) at f g
  have hfg : e.inv ≫ f = e.inv ≫ g := by
    apply Limits.Sigma.hom_ext
    intro p
    exact h p
  exact (cancel_epi e.inv).mp hfg

theorem terminalWeightFaceZero_compat
    (D : J ⥤ SSet.{max uJ vJ w}) (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (terminalWeightRowDegreeIso D a (n + 1)).hom ≫
        (CategoryBar.simplicialReplacementData
          (wbarDegreeCoefficient D a)).δ 0 =
      (wbarRowData D a).δ 0 ≫
        (terminalWeightRowDegreeIso D a n).hom := by
  apply wbarRow_hom_ext D a (n + 1)
  rintro ⟨s, w⟩
  let p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) := ⟨s, w⟩
  let p' := StrictOrdinaryWeightedBar.wFaceZeroIdx
    (CategoryBar.replUnit J) n p
  let c := (SrepBridge.srepFaceZeroComponent D s).app a
  let ιp := wbarRowIncl D a (n + 1) p
  let ιp' := wbarRowIncl D a n p'
  let rp := terminalWeightReplIncl D a (n + 1) p
  let rp' := terminalWeightReplIncl D a n p'
  have hsrc : ιp ≫ (wbarRowData D a).δ 0 = c ≫ ιp' := by
    change wbarRowIncl D a (n + 1) p ≫
      (wbarRowData D a).δ 0 = c ≫ wbarRowIncl D a n p'
    rw [wbarRowIncl_eq_wbarIncl_app,
      wbarRowIncl_eq_wbarIncl_app]
    change _ ≫ (StrictOrdinaryWeightedBar.wbarδ
      (CategoryBar.replUnit J) D n 0).app a = _
    rw [StrictOrdinaryWeightedBar.wbarδ_zero]
    exact congrArg (fun q => q.app a)
      (StrictOrdinaryWeightedBar.wbarFaceZero_ι
        (CategoryBar.replUnit J) D n p)
  dsimp only [p, p', ιp, ιp'] at hsrc
  have htgt : rp ≫
      (CategoryBar.simplicialReplacementData
        (wbarDegreeCoefficient D a)).δ 0 = c ≫ rp' := by
    apply ConcreteCategory.hom_ext
    intro x
    let y : CategoryBar.barObj J (CategoryBar.replUnit J)
        (wbarDegreeCoefficient D a) (n + 1) := ⟨s, x, w⟩
    change CategoryBar.barδ (R := CategoryBar.replUnit J)
      (L := wbarDegreeCoefficient D a) 0 y = _
    rw [CategoryBar.barδ_zero_eq y]
    rfl
  dsimp only [p, p', rp, rp'] at htgt
  dsimp only [p']
  rw [← Category.assoc,
    terminalWeightRowDegreeIso_hom_rowIncl D a (n + 1) ⟨s, w⟩,
    htgt,
    ← terminalWeightRowDegreeIso_hom_rowIncl D a n p']
  exact congrArg (fun z => z ≫ (terminalWeightRowDegreeIso D a n).hom)
    hsrc.symm

theorem terminalWeightFaceLast_compat
    (D : J ⥤ SSet.{max uJ vJ w}) (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (terminalWeightRowDegreeIso D a (n + 1)).hom ≫
        (CategoryBar.simplicialReplacementData
          (wbarDegreeCoefficient D a)).δ (Fin.last (n + 1)) =
      (wbarRowData D a).δ (Fin.last (n + 1)) ≫
        (terminalWeightRowDegreeIso D a n).hom := by
  apply wbarRow_hom_ext D a (n + 1)
  rintro ⟨s, w⟩
  let p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) := ⟨s, w⟩
  let p' := StrictOrdinaryWeightedBar.wFaceLastIdx
    (CategoryBar.replUnit J) n p
  let c := (SrepBridge.srepFaceLastComponent D s).app a
  let ιp := wbarRowIncl D a (n + 1) p
  let ιp' := wbarRowIncl D a n p'
  let rp := terminalWeightReplIncl D a (n + 1) p
  let rp' := terminalWeightReplIncl D a n p'
  have hsrc : ιp ≫ (wbarRowData D a).δ (Fin.last (n + 1)) =
      c ≫ ιp' := by
    change wbarRowIncl D a (n + 1) p ≫
      (wbarRowData D a).δ (Fin.last (n + 1)) =
        c ≫ wbarRowIncl D a n p'
    rw [wbarRowIncl_eq_wbarIncl_app,
      wbarRowIncl_eq_wbarIncl_app]
    change _ ≫ (StrictOrdinaryWeightedBar.wbarδ
      (CategoryBar.replUnit J) D n (Fin.last (n + 1))).app a = _
    rw [StrictOrdinaryWeightedBar.wbarδ_last]
    exact congrArg (fun z => z.app a)
      (StrictOrdinaryWeightedBar.wbarFaceLast_ι
        (CategoryBar.replUnit J) D n p)
  dsimp only [p, p', ιp, ιp'] at hsrc
  have htgt : rp ≫
      (CategoryBar.simplicialReplacementData
        (wbarDegreeCoefficient D a)).δ (Fin.last (n + 1)) =
      c ≫ rp' := by
    apply ConcreteCategory.hom_ext
    intro x
    let y : CategoryBar.barObj J (CategoryBar.replUnit J)
        (wbarDegreeCoefficient D a) (n + 1) := ⟨s, x, w⟩
    change CategoryBar.barδ (R := CategoryBar.replUnit J)
      (L := wbarDegreeCoefficient D a) (Fin.last (n + 1)) y = _
    rw [CategoryBar.barδ_last_eq y]
    apply Sigma.ext
    · have hIndex :
          (SimplexCategory.toCat.map
            (SimplexCategory.δ (Fin.last (n + 1)))).toFunctor =
            Fin.castSuccFunctor (n + 1) := by
          exact CategoryTheory.Functor.ext
            (h_obj := fun j => congrFun Fin.succAbove_last j)
      exact congrArg (fun K => s.whiskerLeft K) hIndex
    · exact HEq.rfl
  dsimp only [p, p', rp, rp'] at htgt
  dsimp only [p']
  rw [← Category.assoc,
    terminalWeightRowDegreeIso_hom_rowIncl D a (n + 1) ⟨s, w⟩,
    htgt,
    ← terminalWeightRowDegreeIso_hom_rowIncl D a n p']
  exact congrArg (fun z => z ≫ (terminalWeightRowDegreeIso D a n).hom)
    hsrc.symm

theorem terminalWeightFaceInner_compat
    (D : J ⥤ SSet.{max uJ vJ w}) (a : SimplexCategoryᵒᵖ) {n : ℕ}
    (q : Fin n) :
    (terminalWeightRowDegreeIso D a (n + 1)).hom ≫
        (CategoryBar.simplicialReplacementData
          (wbarDegreeCoefficient D a)).δ q.castSucc.succ =
      (wbarRowData D a).δ q.castSucc.succ ≫
        (terminalWeightRowDegreeIso D a n).hom := by
  apply wbarRow_hom_ext D a (n + 1)
  rintro ⟨s, w⟩
  have h0 : q.castSucc.succ ≠ (0 : Fin (n + 2)) := by
    apply Fin.ne_of_val_ne
    simp
  have hlast : q.castSucc.succ ≠ Fin.last (n + 1) := by
    apply Fin.ne_of_val_ne
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last, ne_eq,
      Nat.add_right_cancel_iff]
    exact q.isLt.ne
  let p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) := ⟨s, w⟩
  let p' := StrictOrdinaryWeightedBar.wFaceInnerIdx
    (CategoryBar.replUnit J) n q.castSucc.succ hlast p
  let c := (StrictOrdinaryWeightedBar.wFaceInnerComponent
    D q.castSucc.succ h0 s).app a
  let ιp := wbarRowIncl D a (n + 1) p
  let ιp' := wbarRowIncl D a n p'
  let rp := terminalWeightReplIncl D a (n + 1) p
  let rp' := terminalWeightReplIncl D a n p'
  have hsrc : ιp ≫ (wbarRowData D a).δ q.castSucc.succ =
      c ≫ ιp' := by
    change wbarRowIncl D a (n + 1) p ≫
      (wbarRowData D a).δ q.castSucc.succ =
        c ≫ wbarRowIncl D a n p'
    rw [wbarRowIncl_eq_wbarIncl_app,
      wbarRowIncl_eq_wbarIncl_app]
    change _ ≫ (StrictOrdinaryWeightedBar.wbarδ
      (CategoryBar.replUnit J) D n q.castSucc.succ).app a = _
    rw [StrictOrdinaryWeightedBar.wbarδ_inner _ _ _ _ h0 hlast]
    exact congrArg (fun z => z.app a)
      (StrictOrdinaryWeightedBar.wbarFaceInner_ι
        (CategoryBar.replUnit J) D n q.castSucc.succ h0 hlast p)
  dsimp only [p, p', ιp, ιp'] at hsrc
  have htgt : rp ≫
      (CategoryBar.simplicialReplacementData
        (wbarDegreeCoefficient D a)).δ q.castSucc.succ =
      c ≫ rp' := by
    apply ConcreteCategory.hom_ext
    intro x
    let y : CategoryBar.barObj J (CategoryBar.replUnit J)
        (wbarDegreeCoefficient D a) (n + 1) := ⟨s, x, w⟩
    change CategoryBar.barδ (R := CategoryBar.replUnit J)
      (L := wbarDegreeCoefficient D a) q.castSucc.succ y = _
    rw [CategoryBar.barδ_castSucc_succ_eq q y]
    apply Sigma.ext
    · rfl
    · exact HEq.rfl
  dsimp only [p, p', rp, rp'] at htgt
  dsimp only [p']
  rw [← Category.assoc,
    terminalWeightRowDegreeIso_hom_rowIncl D a (n + 1) ⟨s, w⟩,
    htgt,
    ← terminalWeightRowDegreeIso_hom_rowIncl D a n p']
  exact congrArg (fun z => z ≫ (terminalWeightRowDegreeIso D a n).hom)
    hsrc.symm

theorem terminalWeightFace_compat
    (D : J ⥤ SSet.{max uJ vJ w}) (a : SimplexCategoryᵒᵖ)
    {n : ℕ} (i : Fin (n + 2)) :
    (terminalWeightRowDegreeIso D a (n + 1)).hom ≫
        (CategoryBar.simplicialReplacementData
          (wbarDegreeCoefficient D a)).δ i =
      (wbarRowData D a).δ i ≫
        (terminalWeightRowDegreeIso D a n).hom := by
  refine Fin.cases (terminalWeightFaceZero_compat D a n) ?_ i
  intro j
  refine Fin.lastCases (terminalWeightFaceLast_compat D a n) ?_ j
  intro q
  exact terminalWeightFaceInner_compat D a q

theorem terminalWeightDegeneracy_compat
    (D : J ⥤ SSet.{max uJ vJ w}) (a : SimplexCategoryᵒᵖ)
    {n : ℕ} (i : Fin (n + 1)) :
    (terminalWeightRowDegreeIso D a n).hom ≫
        (CategoryBar.simplicialReplacementData
          (wbarDegreeCoefficient D a)).σ i =
      (wbarRowData D a).σ i ≫
        (terminalWeightRowDegreeIso D a (n + 1)).hom := by
  apply wbarRow_hom_ext D a n
  rintro ⟨s, w⟩
  let p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n := ⟨s, w⟩
  let p' := StrictOrdinaryWeightedBar.wDegInnerIdx
    (CategoryBar.replUnit J) n i p
  let c := (StrictOrdinaryWeightedBar.wDegInnerComponent D i s).app a
  let ιp := wbarRowIncl D a n p
  let ιp' := wbarRowIncl D a (n + 1) p'
  let rp := terminalWeightReplIncl D a n p
  let rp' := terminalWeightReplIncl D a (n + 1) p'
  have hsrc : ιp ≫ (wbarRowData D a).σ i = c ≫ ιp' := by
    change wbarRowIncl D a n p ≫ (wbarRowData D a).σ i =
      c ≫ wbarRowIncl D a (n + 1) p'
    rw [wbarRowIncl_eq_wbarIncl_app,
      wbarRowIncl_eq_wbarIncl_app]
    exact congrArg (fun z => z.app a)
      (StrictOrdinaryWeightedBar.wbarσ_ι
        (CategoryBar.replUnit J) D n i p)
  dsimp only [p, p', ιp, ιp'] at hsrc
  have htgt : rp ≫
      (CategoryBar.simplicialReplacementData
        (wbarDegreeCoefficient D a)).σ i = c ≫ rp' := by
    apply ConcreteCategory.hom_ext
    intro x
    let y : CategoryBar.barObj J (CategoryBar.replUnit J)
        (wbarDegreeCoefficient D a) n := ⟨s, x, w⟩
    change CategoryBar.barσ (R := CategoryBar.replUnit J)
      (L := wbarDegreeCoefficient D a) i y = _
    unfold CategoryBar.barσ
    apply Sigma.ext
    · rfl
    · exact HEq.rfl
  dsimp only [p, p', rp, rp'] at htgt
  dsimp only [p']
  rw [← Category.assoc,
    terminalWeightRowDegreeIso_hom_rowIncl D a n ⟨s, w⟩,
    htgt,
    ← terminalWeightRowDegreeIso_hom_rowIncl D a (n + 1) p']
  exact congrArg
    (fun z => z ≫ (terminalWeightRowDegreeIso D a (n + 1)).hom)
    hsrc.symm

/-- Data-level terminal-weight row comparison. -/
noncomputable def terminalWeightRowDataIso (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) :
    wbarRowData D a ≅
      CategoryBar.simplicialReplacementData (wbarDegreeCoefficient D a) :=
  SimplicialObject.Data.isoOfIso
    (terminalWeightRowDegreeIso D a)
    (terminalWeightFace_compat D a)
    (terminalWeightDegeneracy_compat D a)

/-- The data presentation of simplicial replacement is canonically its
packaged simplicial set. -/
noncomputable def terminalWeightReplacementIso (L : J ⥤ Type (max uJ vJ w)) :
    (CategoryBar.simplicialReplacementData L).toSimplicialObject ≅
      CategoryBar.simplicialReplacement L := by
  change CategoryBar.categoryBar (R := CategoryBar.replUnit J) (L := L) ≅
    CategoryBar.categoryBar (R := CategoryBar.replUnit J) (L := L)
  exact Iso.refl _

@[simp]
theorem terminalWeightReplacementIso_hom_app_mk
    (L : J ⥤ Type (max uJ vJ w)) (n : ℕ) :
    (terminalWeightReplacementIso L).hom.app (op ⦋n⦌) = 𝟙 _ :=
  rfl

@[simp]
theorem terminalWeightReplacementIso_inv_app_mk
    (L : J ⥤ Type (max uJ vJ w)) (n : ℕ) :
    (terminalWeightReplacementIso L).inv.app (op ⦋n⦌) = 𝟙 _ :=
  rfl

/-- Simplicial comparison between a fixed inner weighted-bar row and the
ordinary simplicial replacement of the evaluated diagram. -/
noncomputable def terminalWeightRowIso (D : J ⥤ SSet.{max uJ vJ w})
    (a : SimplexCategoryᵒᵖ) :
    wbarRow D a ≅
      CategoryBar.simplicialReplacement (wbarDegreeCoefficient D a) :=
  (SimplicialObject.Data.toSimplicialFunctor (C := Type (max uJ vJ w))).mapIso
    (terminalWeightRowDataIso D a) ≪≫
      terminalWeightReplacementIso (wbarDegreeCoefficient D a)

@[simp]
theorem terminalWeightRowIso_hom_app_mk
    (D : J ⥤ SSet.{max uJ vJ w}) (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (terminalWeightRowIso D a).hom.app (op ⦋n⦌) =
      (terminalWeightRowDegreeIso D a n).hom :=
  rfl

@[simp]
theorem terminalWeightRowIso_inv_app_mk
    (D : J ⥤ SSet.{max uJ vJ w}) (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (terminalWeightRowIso D a).inv.app (op ⦋n⦌) =
      (terminalWeightRowDegreeIso D a n).inv :=
  rfl

/-- The simplicial row comparison has the expected value on every explicit
evaluated row inclusion. -/
@[reassoc]
theorem terminalWeightRowIso_hom_rowIncl
    (D : J ⥤ SSet.{max uJ vJ w}) (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    wbarRowIncl D a n p ≫
        (terminalWeightRowIso D a).hom.app (op ⦋n⦌) =
      terminalWeightReplIncl D a n p := by
  rw [terminalWeightRowIso_hom_app_mk]
  exact terminalWeightRowDegreeIso_hom_rowIncl D a n p

/-- Data-level evaluation of the BK1 weighted-bar augmentation. -/
noncomputable def wbarRowAugmentationData
    {D : J ⥤ SSet.{max uJ vJ w}} {Z : SSet.{max uJ vJ w}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ) :
    wbarRowData D a ⟶ SimplicialObject.Data.constData (Z.obj a) :=
  SimplicialObject.Data.evalHom a (wbarAugmentationDataOf τ)

@[simp]
theorem wbarRowAugmentationData_app
    {D : J ⥤ SSet.{max uJ vJ w}} {Z : SSet.{max uJ vJ w}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ)
    (n : ℕ) :
    (wbarRowAugmentationData τ a).app n =
      (StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit J) D n
          (fun p => τ.app p.1.left)).app a := by
  change ((wbarAugmentationDataOf τ).app n).app a = _
  rw [wbarAugmentationDataOf_app]

/-- The BK1 weighted-bar augmentation evaluated in a fixed inner degree. -/
noncomputable def wbarRowAugmentation {D : J ⥤ SSet.{max uJ vJ w}} {Z : SSet.{max uJ vJ w}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ) :
    wbarRow D a ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (Z.obj a) :=
  (SimplicialObject.Data.toSimplicialFunctor (C := Type (max uJ vJ w))).map
      (wbarRowAugmentationData τ a) ≫
    (SimplicialObject.Data.constDataIso (Z.obj a)).hom

/-- Evaluating the weighted-bar augmentation agrees strictly with the
augmentation of the evaluated row. -/
@[reassoc]
theorem wbarRowEvaluationIso_hom_comp_rowAugmentation
    {D : J ⥤ SSet.{max uJ vJ w}} {Z : SSet.{max uJ vJ w}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ) :
    (wbarRowEvaluationIso D a).hom ≫ wbarRowAugmentation τ a =
      Functor.whiskerRight (wbarAugmentationOf τ)
        ((evaluation SimplexCategoryᵒᵖ (Type (max uJ vJ w))).obj a) := by
  ext b x
  induction b using Opposite.rec with
  | _ b =>
      induction b using SimplexCategory.rec with
      | _ n => rfl

/-- The corresponding augmentation on the ordinary simplicial replacement,
defined by transporting the evaluated BK1 augmentation across the row iso. -/
noncomputable def terminalWeightDegreeAugmentation
    {D : J ⥤ SSet.{max uJ vJ w}} {Z : SSet.{max uJ vJ w}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ) :
    CategoryBar.simplicialReplacement (wbarDegreeCoefficient D a) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (Z.obj a) :=
  (terminalWeightRowIso D a).inv ≫ wbarRowAugmentation τ a

/-- The evaluated BK1 augmentation is exactly the row comparison followed by
the transported degree augmentation. -/
@[reassoc]
theorem terminalWeightRowIso_hom_comp_degreeAugmentation
    {D : J ⥤ SSet.{max uJ vJ w}} {Z : SSet.{max uJ vJ w}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ) :
    (terminalWeightRowIso D a).hom ≫
        terminalWeightDegreeAugmentation τ a =
      wbarRowAugmentation τ a := by
  simp [terminalWeightDegreeAugmentation]

/-- Exact evaluation of the row augmentation on every weighted summand. -/
@[reassoc]
theorem wbarRowAugmentation_ι
    {D : J ⥤ SSet.{max uJ vJ w}} {Z : SSet.{max uJ vJ w}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ)
    (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit J) D n p).app a ≫
      (wbarRowAugmentation τ a).app (op ⦋n⦌) =
      (τ.app p.1.left).app a := by
  rw [← wbarRowIncl_eq_wbarIncl_app D a n p]
  unfold wbarRowAugmentation
  change
    wbarRowIncl D a n p ≫
        ((wbarRowAugmentationData τ a).app n ≫ 𝟙 _) = _
  rw [Category.comp_id]
  rw [wbarRowAugmentationData_app]
  change
    wbarRowIncl D a n p ≫
        (StrictOrdinaryWeightedBar.wbarDesc
          (CategoryBar.replUnit J) D n
            (fun p => τ.app p.1.left)).app a = _
  rw [wbarRowIncl_eq_wbarIncl_app]
  exact congrArg (fun q => q.app a)
    (StrictOrdinaryWeightedBar.wbarDesc_ι
      (CategoryBar.replUnit J) D n (fun p => τ.app p.1.left) p)

/-- Exact row-augmentation formula using the explicit evaluated row
inclusion. -/
@[reassoc]
theorem wbarRowAugmentation_rowIncl
    {D : J ⥤ SSet.{max uJ vJ w}} {Z : SSet.{max uJ vJ w}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ)
    (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    wbarRowIncl D a n p ≫
        (wbarRowAugmentation τ a).app (op ⦋n⦌) =
      (τ.app p.1.left).app a := by
  rw [wbarRowIncl_eq_wbarIncl_app]
  exact wbarRowAugmentation_ι τ a n p

/-- The transported degree augmentation projects an explicit replacement
summand through the cocone map at the left endpoint of its chain. -/
@[reassoc]
theorem terminalWeightReplIncl_comp_degreeAugmentation
    {D : J ⥤ SSet.{max uJ vJ w}} {Z : SSet.{max uJ vJ w}}
    (τ : D ⟶ (Functor.const J).obj Z)
    (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n) :
    terminalWeightReplIncl D a n p ≫
        (terminalWeightDegreeAugmentation τ a).app (op ⦋n⦌) =
      (τ.app p.1.left).app a := by
  calc
    terminalWeightReplIncl D a n p ≫
          (terminalWeightDegreeAugmentation τ a).app (op ⦋n⦌) =
        (wbarRowIncl D a n p ≫
            (terminalWeightRowIso D a).hom.app (op ⦋n⦌)) ≫
          (terminalWeightDegreeAugmentation τ a).app (op ⦋n⦌) := by
            exact congrArg (fun q => q ≫
              (terminalWeightDegreeAugmentation τ a).app (op ⦋n⦌))
                (terminalWeightRowIso_hom_rowIncl D a n p).symm
    _ = wbarRowIncl D a n p ≫
          (wbarRowAugmentation τ a).app (op ⦋n⦌) := by
            calc
              _ = wbarRowIncl D a n p ≫
                  ((terminalWeightRowIso D a).hom.app (op ⦋n⦌) ≫
                    (terminalWeightDegreeAugmentation τ a).app
                      (op ⦋n⦌)) := Category.assoc _ _ _
              _ = wbarRowIncl D a n p ≫
                  ((terminalWeightRowIso D a).hom ≫
                    terminalWeightDegreeAugmentation τ a).app
                      (op ⦋n⦌) := rfl
              _ = _ := congrArg (fun q => wbarRowIncl D a n p ≫ q)
                (NatTrans.congr_app
                  (terminalWeightRowIso_hom_comp_degreeAugmentation τ a)
                  (op ⦋n⦌))
    _ = (τ.app p.1.left).app a :=
      wbarRowAugmentation_rowIncl τ a n p

end SSet.BousfieldKanRowsOf

end
