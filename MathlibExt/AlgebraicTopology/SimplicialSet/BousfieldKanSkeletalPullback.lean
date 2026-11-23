/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointPullback
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanNerveProjection
public import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialSkeletalFiltration
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import MathlibExt.CategoryTheory.NerveCommonHom
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationPullbackMono
import MathlibExt.CategoryTheory.CategoryBar.ElementsComparison
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

/-!
# Actual skeletal pullbacks of the Bousfield–Kan projection

The outer bar filtration is identified with the preimage of the actual nerve
skeleton. Realization then preserves its strict square along the genuine
mono skeleton inclusion. No weak transition hypothesis is needed for these
geometric identifications, and no whole nerve-cell characteristic map is
assumed mono.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace SSet

private theorem mem_skeleton_iff_bounded_factor
    (X : SSet.{u}) (d m : ℕ) (z : X.obj (op ⦋m⦌)) :
    z ∈ (X.skeleton d).obj (op ⦋m⦌) ↔
      ∃ (k : ℕ) (_ : k < d) (y : X.obj (op ⦋k⦌)) (θ : ⦋m⦌ ⟶ ⦋k⦌),
        z = X.map θ.op y := by
  constructor
  · intro hz
    obtain ⟨k, θ, hθ, y, hy⟩ := X.exists_nonDegenerate z
    let _ : Epi θ := hθ
    have hsupport : Subcomplex.ofSimplex y.1 ≤ X.skeleton d := by
      rw [← Subcomplex.ofSimplex_map_of_epi θ y.1, ← hy]
      exact (Subcomplex.ofSimplex_le_iff z (X.skeleton d)).mpr hz
    have hySk : y.1 ∈ (X.skeleton d).obj (op ⦋k⦌) :=
      hsupport _ (Subcomplex.mem_ofSimplex_obj y.1)
    exact ⟨k, (X.mem_skeleton_obj_iff_of_nonDegenerate y d).mp hySk, y.1, θ, hy⟩
  · rintro ⟨k, hk, y, θ, rfl⟩
    exact (X.skeleton d).map θ.op (X.mem_skeleton y hk)

private theorem diagonalFiltration_mem_iff_row_skeleton
    (T : SimplicialObject SSet.{u}) (n m : ℕ)
    (z : (simplicialDiagonalFunctor.obj T).obj (op ⦋m⦌)) :
    z ∈ (diagonalFiltration T n).obj (op ⦋m⦌) ↔
      z ∈ ((simplicialRow T (op ⦋m⦌)).skeleton (n + 1)).obj (op ⦋m⦌) := by
  constructor
  · intro hz
    obtain ⟨k, hk, y, θ, hy⟩ := (mem_diagonalFiltration_iff T n m z).mp hz
    exact (mem_skeleton_iff_bounded_factor (simplicialRow T (op ⦋m⦌)) (n + 1) m z).mpr
      ⟨k, Nat.lt_succ_of_le hk, y, θ, hy⟩
  · intro hz
    obtain ⟨k, hk, y, θ, hy⟩ :=
      (mem_skeleton_iff_bounded_factor (simplicialRow T (op ⦋m⦌)) (n + 1) m z).mp hz
    exact (mem_diagonalFiltration_iff T n m z).mpr
      ⟨k, Nat.le_of_lt_succ hk, y, θ, hy⟩

private theorem skeleton_preimage_of_cartesian_epi
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (hcart : ∀ (m k : ℕ) (θ : ⦋m⦌ ⟶ ⦋k⦌) [Epi θ],
      IsPullback (X.map θ.op) (f.app (op ⦋k⦌))
        (f.app (op ⦋m⦌)) (Y.map θ.op)) (d : ℕ) :
    (Y.skeleton d).preimage f = X.skeleton d := by
  ext ⟨⟨m⟩⟩ z
  constructor
  · intro hz
    change f.app (op ⦋m⦌) z ∈ (Y.skeleton d).obj (op ⦋m⦌) at hz
    obtain ⟨k, θ, hθ, y, hy⟩ := Y.exists_nonDegenerate (f.app (op ⦋m⦌) z)
    let _ : Epi θ := hθ
    have hsupport : Subcomplex.ofSimplex y.1 ≤ Y.skeleton d := by
      rw [← Subcomplex.ofSimplex_map_of_epi θ y.1, ← hy]
      exact (Subcomplex.ofSimplex_le_iff (f.app (op ⦋m⦌) z) (Y.skeleton d)).mpr hz
    have hySk : y.1 ∈ (Y.skeleton d).obj (op ⦋k⦌) :=
      hsupport _ (Subcomplex.mem_ofSimplex_obj y.1)
    have hk : k < d := (Y.mem_skeleton_obj_iff_of_nonDegenerate y d).mp hySk
    obtain ⟨x, hx, _hxbase⟩ := Types.exists_of_isPullback (hcart m k θ) z y.1 hy
    apply (mem_skeleton_iff_bounded_factor X d m z).mpr
    exact ⟨k, hk, x, θ, hx.symm⟩
  · intro hz
    obtain ⟨k, hk, y, θ, rfl⟩ := (mem_skeleton_iff_bounded_factor X d m z).mp hz
    change f.app (op ⦋m⦌) (X.map θ.op y) ∈ (Y.skeleton d).obj (op ⦋m⦌)
    rw [f.naturality_apply]
    exact (Y.skeleton d).map θ.op (Y.mem_skeleton (f.app (op ⦋k⦌) y) hk)

private theorem simplex_epi_zero {m k : ℕ} (θ : ⦋m⦌ ⟶ ⦋k⦌) [Epi θ] :
    θ.toOrderHom 0 = 0 := by
  obtain ⟨i, hi⟩ := (SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi θ)) 0
  apply le_antisymm
  · calc
      θ.toOrderHom 0 ≤ θ.toOrderHom i := θ.toOrderHom.monotone (Fin.zero_le i)
      _ = 0 := hi
  · exact Fin.zero_le _

private theorem elementsCoefficientPair_heq {J : Type u} [Category.{v} J]
    (L : J ⥤ Type (max u v)) (x y : L.Elements) (h : x = y) :
    HEq (x.val, (PUnit.unit : PUnit.{1})) (y.val, (PUnit.unit : PUnit.{1})) := by
  cases h
  rfl

private theorem elementsChain_ext {J : Type u} [Category.{v} J]
    (L : J ⥤ Type (max u v)) {n : ℕ} (G H : ComposableArrows L.Elements n)
    (hbase : G ⋙ Functor.Elements.π L = H ⋙ Functor.Elements.π L)
    (hzero : G.obj (0 : Fin (n + 1)) = H.obj (0 : Fin (n + 1))) : G = H := by
  apply ((CategoryBar.replElementsEquiv J L n).symm).injective
  change (⟨G ⋙ Functor.Elements.π L, (G.obj 0).val, PUnit.unit⟩ : CategoryBar.replObj J L n) =
    ⟨H ⋙ Functor.Elements.π L, (H.obj 0).val, PUnit.unit⟩
  exact Sigma.ext hbase (elementsCoefficientPair_heq L _ _ hzero)

private theorem elementsNerveProjection_isPullback_epi
    {J : Type u} [Category.{v} J] (L : J ⥤ Type (max u v))
    (m k : ℕ) (θ : ⦋m⦌ ⟶ ⦋k⦌) [Epi θ] :
    IsPullback ((nerve L.Elements).map θ.op)
      ((nerveMapCommonHom.{u, v, 0} (Functor.Elements.π L)).app (op ⦋k⦌))
      ((nerveMapCommonHom.{u, v, 0} (Functor.Elements.π L)).app (op ⦋m⦌)) ((nerve J).map θ.op) := by
  have hθ₀ := simplex_epi_zero θ
  rw [Types.isPullback_iff]
  refine ⟨(nerveMapCommonHom.{u, v, 0} (Functor.Elements.π L)).naturality θ.op, ?_, ?_⟩
  · intro G H h
    have hzero := Functor.congr_obj h.1 (0 : Fin (m + 1))
    change G.obj (θ.toOrderHom 0) = H.obj (θ.toOrderHom 0) at hzero
    rw [hθ₀] at hzero
    exact elementsChain_ext L G H h.2 hzero
  · intro G c h
    change G ⋙ Functor.Elements.π L = (nerve J).map θ.op c at h
    have hfirst : (G.obj (0 : Fin (m + 1))).obj = c.left := by
      have ho := Functor.congr_obj h (0 : Fin (m + 1))
      change (G.obj 0).obj = c.obj (θ.toOrderHom 0) at ho
      rw [hθ₀] at ho
      exact ho.trans (SrepBridge.srepLeftZero c).symm
    let l : L.obj c.left := L.map (eqToHom hfirst) (G.obj (0 : Fin (m + 1))).val
    let H : ComposableArrows L.Elements k :=
      CategoryBar.replElementsEquiv J L k ⟨c, l, PUnit.unit⟩
    have hbaseH : H ⋙ Functor.Elements.π L = c := rfl
    have hbase : ((nerve L.Elements).map θ.op H) ⋙ Functor.Elements.π L =
        G ⋙ Functor.Elements.π L := by
      change (nerve J).map θ.op (H ⋙ Functor.Elements.π L) = G ⋙ Functor.Elements.π L
      exact (congrArg (fun c : ComposableArrows J k => (nerve J).map θ.op c) hbaseH).trans h.symm
    have hzero : ((nerve L.Elements).map θ.op H).obj (0 : Fin (m + 1)) =
        G.obj (0 : Fin (m + 1)) := by
      have he : ((nerve L.Elements).map θ.op H).obj (0 : Fin (m + 1)) = H.obj 0 := by
        change H.obj (θ.toOrderHom 0) = H.obj 0
        rw [hθ₀]
      rw [he]
      change L.elementsMk c.left (L.map (c.map' 0 0) l) = G.obj 0
      rw [c.map'_self 0, L.map_id]
      apply Functor.Elements.ext _ _ hfirst.symm
      change L.map (eqToHom hfirst.symm) (L.map (eqToHom hfirst) (G.obj 0).val) =
        (G.obj 0).val
      rw [← Functor.map_comp_apply]
      simp
    exact ⟨H, elementsChain_ext L _ _ hbase hzero, hbaseH⟩

private abbrev bkOuterBar {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    SimplicialObject SSet.{max u v} :=
  StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D

private theorem bkFixedRowProjection_isPullback_epi
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (a : SimplexCategoryᵒᵖ)
    (m k : ℕ) (θ : ⦋m⦌ ⟶ ⦋k⦌) [Epi θ] :
    IsPullback ((simplicialRow (bkOuterBar D) a).map θ.op)
      ((bkFixedRowProjection D a).app (op ⦋k⦌))
      ((bkFixedRowProjection D a).app (op ⦋m⦌)) ((nerve J).map θ.op) := by
  apply (elementsNerveProjection_isPullback_epi (wbarDegreeCoefficient D a) m k θ).of_iso
    ((bkFixedRowIso D a).app (op ⦋k⦌)).symm
    ((bkFixedRowIso D a).app (op ⦋m⦌)).symm (Iso.refl _) (Iso.refl _)
  · exact (bkFixedRowIso D a).inv.naturality θ.op
  · simp only [bkFixedRowProjection, NatTrans.comp_app, Iso.symm_hom, Iso.refl_hom,
      Iso.app_inv, Category.comp_id, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  · simp only [bkFixedRowProjection, NatTrans.comp_app, Iso.symm_hom, Iso.refl_hom,
      Iso.app_inv, Category.comp_id, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  · simp

/-- The actual outer bar filtration of the Bousfield–Kan diagonal through
degree `n`. Its base stage is the topological `n`-skeleton, bound `n + 1`. -/
def bkSkeletalFiltration {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) : (bkHocolim D).Subcomplex :=
  diagonalFiltration (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D) n

/-- The actual outer BK stage is the preimage of the actual nerve skeleton.
This equality holds for arbitrary diagrams and arbitrary indexing categories
with small hom sets; nonregular nerve cells are allowed. -/
theorem bkSkeletalFiltration_eq_preimage {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkSkeletalFiltration D n = ((nerve J).skeleton (n + 1)).preimage (bkHocolimToNerve D) := by
  ext ⟨⟨m⟩⟩ z
  change z ∈ (diagonalFiltration (bkOuterBar D) n).obj (op ⦋m⦌) ↔
    (bkHocolimToNerve D).app (op ⦋m⦌) z ∈ ((nerve J).skeleton (n + 1)).obj (op ⦋m⦌)
  have hs := skeleton_preimage_of_cartesian_epi (bkFixedRowProjection D (op ⦋m⦌))
    (bkFixedRowProjection_isPullback_epi D (op ⦋m⦌)) (n + 1)
  have hp := congrArg
    (fun A : (simplicialRow (bkOuterBar D) (op ⦋m⦌)).Subcomplex => z ∈ A.obj (op ⦋m⦌)) hs
  have hπ := ConcreteCategory.congr_hom (bkFixedRowProjection_diagonal D m) z
  constructor
  · intro hz
    have hr := (diagonalFiltration_mem_iff_row_skeleton (bkOuterBar D) n m z).mp hz
    have hpre := Eq.mpr hp hr
    change (bkFixedRowProjection D (op ⦋m⦌)).app (op ⦋m⦌) z ∈
      ((nerve J).skeleton (n + 1)).obj (op ⦋m⦌) at hpre
    exact hπ ▸ hpre
  · intro hz
    have hpre := hπ.symm ▸ hz
    change z ∈ (((nerve J).skeleton (n + 1)).preimage
      (bkFixedRowProjection D (op ⦋m⦌))).obj (op ⦋m⦌) at hpre
    exact (diagonalFiltration_mem_iff_row_skeleton (bkOuterBar D) n m z).mpr (Eq.mp hp hpre)

/-- The actual projection from the outer BK stage to the nerve skeleton. -/
def bkSkeletalProjection {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (bkSkeletalFiltration D n : SSet.{max u v}) ⟶ ((nerve J).skeleton (n + 1) : SSet.{max u v}) :=
  (Subcomplex.eqToIso (bkSkeletalFiltration_eq_preimage D n)).hom ≫
    ((nerve J).skeleton (n + 1)).fromPreimage (bkHocolimToNerve D)

@[reassoc]
theorem bkSkeletalProjection_comp_ι {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkSkeletalProjection D n ≫ ((nerve J).skeleton (n + 1)).ι =
      (bkSkeletalFiltration D n).ι ≫ bkHocolimToNerve D := by
  rw [bkSkeletalProjection, Category.assoc, Subcomplex.fromPreimage_ι,
    ← Category.assoc, Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι]

/-- The BK outer stage is the actual strict simplicial skeleton pullback. -/
theorem bkSkeletalProjection_isPullback {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsPullback (bkSkeletalFiltration D n).ι (bkSkeletalProjection D n)
      (bkHocolimToNerve D) ((nerve J).skeleton (n + 1)).ι := by
  let e := Subcomplex.eqToIso (bkSkeletalFiltration_eq_preimage D n)
  apply (Subcomplex.preimage_isPullback ((nerve J).skeleton (n + 1)) (bkHocolimToNerve D)).of_iso
    e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [e, Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      Subcomplex.eqToIso_inv, Subcomplex.homOfLE_ι]
  · simp only [bkSkeletalProjection, e, Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · simp
  · simp

/-- Realization preserves this strict square along the genuine mono nerve
skeleton inclusion, without a monomorphism premise on any characteristic cell. -/
theorem bkSkeletalProjection_realized_isPullback {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsPullback (toTop.map (bkSkeletalFiltration D n).ι) (toTop.map (bkSkeletalProjection D n))
      (toTop.map (bkHocolimToNerve D)) (toTop.map ((nerve J).skeleton (n + 1)).ι) :=
  ((bkSkeletalProjection_isPullback D n).flip.map_toTop_of_mono).flip

/-- The actual realized outer stage is canonically isomorphic to the literal
topological pullback over the nerve skeleton. -/
def bkSkeletalRestrictionIso {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    toTop.obj (bkSkeletalFiltration D n : SSet.{max u v}) ≅
      pullback (toTop.map (bkHocolimToNerve D)) (toTop.map ((nerve J).skeleton (n + 1)).ι) :=
  (bkSkeletalProjection_realized_isPullback D n).isoIsPullback _ _ (IsPullback.of_hasPullback _ _)

@[reassoc (attr := simp)]
theorem bkSkeletalRestrictionIso_hom_fst {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (bkSkeletalRestrictionIso D n).hom ≫
      pullback.fst (toTop.map (bkHocolimToNerve D)) (toTop.map ((nerve J).skeleton (n + 1)).ι) =
        toTop.map (bkSkeletalFiltration D n).ι :=
  (bkSkeletalProjection_realized_isPullback D n).isoIsPullback_hom_fst _ _
    (IsPullback.of_hasPullback _ _)

@[reassoc (attr := simp)]
theorem bkSkeletalRestrictionIso_hom_snd {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (bkSkeletalRestrictionIso D n).hom ≫
      pullback.snd (toTop.map (bkHocolimToNerve D)) (toTop.map ((nerve J).skeleton (n + 1)).ι) =
        toTop.map (bkSkeletalProjection D n) :=
  (bkSkeletalProjection_realized_isPullback D n).isoIsPullback_hom_snd _ _
    (IsPullback.of_hasPullback _ _)

@[reassoc (attr := simp)]
theorem bkSkeletalRestrictionIso_inv_fst {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (bkSkeletalRestrictionIso D n).inv ≫ toTop.map (bkSkeletalFiltration D n).ι =
      pullback.fst (toTop.map (bkHocolimToNerve D)) (toTop.map ((nerve J).skeleton (n + 1)).ι) :=
  (bkSkeletalProjection_realized_isPullback D n).isoIsPullback_inv_fst _ _
    (IsPullback.of_hasPullback _ _)

@[reassoc (attr := simp)]
theorem bkSkeletalRestrictionIso_inv_snd {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (bkSkeletalRestrictionIso D n).inv ≫ toTop.map (bkSkeletalProjection D n) =
      pullback.snd (toTop.map (bkHocolimToNerve D)) (toTop.map ((nerve J).skeleton (n + 1)).ι) :=
  (bkSkeletalProjection_realized_isPullback D n).isoIsPullback_inv_snd _ _
    (IsPullback.of_hasPullback _ _)

-- BEGIN approved proof-only weighted-filtration characteristic

private theorem bkSkeletalFiltration_eq_diagonalFiltration_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkSkeletalFiltration D n =
      diagonalFiltration (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D)
          n := rfl

/-- The actual BK outer skeletal filtration is the weighted-bar diagonal
filtration in the same degree; the equation keeps the original carrier. -/
theorem bkSkeletalFiltration_eq_diagonalFiltration
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkSkeletalFiltration D n =
      diagonalFiltration (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D) n :=
  bkSkeletalFiltration_eq_diagonalFiltration_aux D n

-- END approved proof-only weighted-filtration characteristic

end SSet

end
