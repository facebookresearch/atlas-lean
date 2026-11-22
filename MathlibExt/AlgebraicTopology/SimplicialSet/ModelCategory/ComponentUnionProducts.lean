/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ComponentUnionWeakRestriction
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents.Products

/-!
# Products and original fibres of selected components

The component comparison uses the native connected-component cofork and
actual degenerate edges. Selected products use the existing Cartesian
subcomplex product. Exact component restrictions of original Kan fibrations
remain fibrations, and their original strict fibres are canonically the same
as the corresponding ambient fibres. No ambient Kan hypothesis is needed
for the fibre Kan and every pointed-group corollaries of a fibration.

These are neutral inputs to the component comparisons in Rezk (2001), 11.6.
They do not assert full mapping-space composition or shear weakness.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Limits Opposite HomotopicalAlgebra MonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

variable {X Y : SSet.{u}}

/-- Literal target selector on the actual pointwise tensor. -/
def componentUnionTensorSelector (X Y : SSet.{u}) (S : Set (π₀ X)) (T : Set (π₀ Y)) :
    Set (π₀ (X ⊗ Y)) := (piZeroTensorEquiv X Y) ⁻¹' (S ×ˢ T)

/-- The selected tensor union is the same existing Cartesian product of subcomplexes. -/
theorem componentUnionTensor_eq_prod (X Y : SSet.{u}) (S : Set (π₀ X)) (T : Set (π₀ Y)) :
    componentUnion (X ⊗ Y) (componentUnionTensorSelector X Y S T) =
      (componentUnion X S).prod (componentUnion Y T) := by
  ext n q
  simp only [componentUnionTensorSelector, Subcomplex.prod_obj, Set.mem_prod,
    mem_componentUnion, Set.mem_preimage, piZeroTensorEquiv_apply, mapπ₀_mk]
  change _ ↔ q.1 ∈ (componentUnion X S).obj n ∧ q.2 ∈ (componentUnion Y T).obj n
  rw [mem_componentUnion, mem_componentUnion]
  rfl

/-- The selected Cartesian tensor isomorphism reuses the native Subcomplex.prodIso. -/
def componentUnionTensorIso (X Y : SSet.{u}) (S : Set (π₀ X)) (T : Set (π₀ Y)) :
    (componentUnion (X ⊗ Y) (componentUnionTensorSelector X Y S T) : SSet.{u}) ≅
      (componentUnion X S : SSet.{u}) ⊗ (componentUnion Y T : SSet.{u}) :=
  Subcomplex.eqToIso (componentUnionTensor_eq_prod X Y S T) ≪≫
    Subcomplex.prodIso (componentUnion X S) (componentUnion Y T)

@[reassoc (attr := simp)]
theorem componentUnionTensorIso_fst (X Y : SSet.{u}) (S : Set (π₀ X)) (T : Set (π₀ Y)) :
    (componentUnionTensorIso X Y S T).hom ≫ CartesianMonoidalCategory.fst _ _ ≫
        (componentUnion X S).ι =
      (componentUnion (X ⊗ Y) (componentUnionTensorSelector X Y S T)).ι ≫
        CartesianMonoidalCategory.fst X Y := by
  simp only [Category.assoc, componentUnionTensorIso, Iso.trans_hom, Subcomplex.eqToIso_hom,
    Subcomplex.prodIso, CartesianMonoidalCategory.lift_fst_assoc,
    Subcomplex.lift_ι, Subcomplex.homOfLE_ι_assoc]

@[reassoc (attr := simp)]
theorem componentUnionTensorIso_snd (X Y : SSet.{u}) (S : Set (π₀ X)) (T : Set (π₀ Y)) :
    (componentUnionTensorIso X Y S T).hom ≫ CartesianMonoidalCategory.snd _ _ ≫
        (componentUnion Y T).ι =
      (componentUnion (X ⊗ Y) (componentUnionTensorSelector X Y S T)).ι ≫
        CartesianMonoidalCategory.snd X Y := by
  simp only [Category.assoc, componentUnionTensorIso, Iso.trans_hom, Subcomplex.eqToIso_hom,
    Subcomplex.prodIso, CartesianMonoidalCategory.lift_snd_assoc,
    Subcomplex.lift_ι, Subcomplex.homOfLE_ι_assoc]

/-- Exact selected component subset of the actual chosen categorical product. -/
def componentUnionProductSelector (X Y : SSet.{u}) (S : Set (π₀ X)) (T : Set (π₀ Y)) :
    Set (π₀ (X ⨯ Y)) := (piZeroProductEquiv X Y) ⁻¹' (S ×ˢ T)

theorem componentUnionProductSelector_tensor (X Y : SSet.{u})
    (S : Set (π₀ X)) (T : Set (π₀ Y)) :
    componentUnionProductSelector X Y S T =
      (mapπ₀ (componentTensorProductIso X Y).inv) ⁻¹'
        componentUnionTensorSelector X Y S T := by rfl

/-- The chosen-product union isomorphism keeps the actual preimage and native product
isomorphisms. -/
def componentUnionProductIso (X Y : SSet.{u}) (S : Set (π₀ X)) (T : Set (π₀ Y)) :
    (componentUnion (X ⨯ Y) (componentUnionProductSelector X Y S T) : SSet.{u}) ≅
      (componentUnion X S : SSet.{u}) ⨯ (componentUnion Y T : SSet.{u}) := by
  let p := componentUnionPreimageMap (componentTensorProductIso X Y).inv
    (componentUnionTensorSelector X Y S T)
  let _ : IsIso p :=
    (componentUnionPreimageMap_isPullback (componentTensorProductIso X Y).inv
      (componentUnionTensorSelector X Y S T)).isIso_snd_of_isIso
  exact Subcomplex.eqToIso (congrArg (componentUnion (X ⨯ Y))
      (componentUnionProductSelector_tensor X Y S T)) ≪≫
    asIso p ≪≫ componentUnionTensorIso X Y S T ≪≫
      componentTensorProductIso (componentUnion X S) (componentUnion Y T)

@[reassoc (attr := simp)]
theorem componentUnionProductIso_fst (X Y : SSet.{u}) (S : Set (π₀ X)) (T : Set (π₀ Y)) :
    (componentUnionProductIso X Y S T).hom ≫ prod.fst ≫ (componentUnion X S).ι =
      (componentUnion (X ⨯ Y) (componentUnionProductSelector X Y S T)).ι ≫ prod.fst := by
  simp only [componentUnionProductIso, Iso.trans_hom, asIso_hom, Category.assoc,
    componentTensorProductIso_fst_assoc, componentUnionTensorIso_fst,
    componentUnionPreimageMap_ι_assoc,
    Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι_assoc,
    componentTensorProductIso_inv_fst]

@[reassoc (attr := simp)]
theorem componentUnionProductIso_snd (X Y : SSet.{u}) (S : Set (π₀ X)) (T : Set (π₀ Y)) :
    (componentUnionProductIso X Y S T).hom ≫ prod.snd ≫ (componentUnion Y T).ι =
      (componentUnion (X ⨯ Y) (componentUnionProductSelector X Y S T)).ι ≫ prod.snd := by
  simp only [componentUnionProductIso, Iso.trans_hom, asIso_hom, Category.assoc,
    componentTensorProductIso_snd_assoc, componentUnionTensorIso_snd,
    componentUnionPreimageMap_ι_assoc,
    Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι_assoc,
    componentTensorProductIso_inv_snd]

@[reassoc (attr := simp)]
theorem componentUnionProductIso_inv_ι (X Y : SSet.{u}) (S : Set (π₀ X)) (T : Set (π₀ Y)) :
    (componentUnionProductIso X Y S T).inv ≫
        (componentUnion (X ⨯ Y) (componentUnionProductSelector X Y S T)).ι =
      prod.map (componentUnion X S).ι (componentUnion Y T).ι := by
  apply (cancel_epi (componentUnionProductIso X Y S T).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply prod.hom_ext
  · simpa only [Category.assoc, prod.map_fst] using
      (componentUnionProductIso_fst X Y S T).symm
  · simpa only [Category.assoc, prod.map_snd] using
      (componentUnionProductIso_snd X Y S T).symm

@[reassoc (attr := simp)]
theorem componentUnionProductIso_hom_ι (X Y : SSet.{u}) (S : Set (π₀ X)) (T : Set (π₀ Y)) :
    (componentUnionProductIso X Y S T).hom ≫
        prod.map (componentUnion X S).ι (componentUnion Y T).ι =
      (componentUnion (X ⨯ Y) (componentUnionProductSelector X Y S T)).ι := by
  apply (cancel_epi (componentUnionProductIso X Y S T).inv).mp
  rw [Iso.inv_hom_id_assoc, componentUnionProductIso_inv_ι]

/-- The forward projection retains the exact original first simplex. -/
theorem componentUnionProductIso_hom_fst_val (X Y : SSet.{u})
    (S : Set (π₀ X)) (T : Set (π₀ Y)) (n : SimplexCategoryᵒᵖ)
    (q : (componentUnion (X ⨯ Y) (componentUnionProductSelector X Y S T)).obj n) :
    ((prod.fst : (componentUnion X S : SSet.{u}) ⨯ (componentUnion Y T : SSet.{u}) ⟶ _).app n
      ((componentUnionProductIso X Y S T).hom.app n q)).val =
        (prod.fst : X ⨯ Y ⟶ X).app n q.val := by
  exact congrArg (fun a => a.app n q) (componentUnionProductIso_fst X Y S T)

/-- The forward projection retains the exact original second simplex. -/
theorem componentUnionProductIso_hom_snd_val (X Y : SSet.{u})
    (S : Set (π₀ X)) (T : Set (π₀ Y)) (n : SimplexCategoryᵒᵖ)
    (q : (componentUnion (X ⨯ Y) (componentUnionProductSelector X Y S T)).obj n) :
    ((prod.snd : (componentUnion X S : SSet.{u}) ⨯ (componentUnion Y T : SSet.{u}) ⟶ _).app n
      ((componentUnionProductIso X Y S T).hom.app n q)).val =
        (prod.snd : X ⨯ Y ⟶ Y).app n q.val := by
  exact congrArg (fun a => a.app n q) (componentUnionProductIso_snd X Y S T)

/-- The inverse map is the exact original product of inclusions in every degree. -/
theorem componentUnionProductIso_inv_val (X Y : SSet.{u})
    (S : Set (π₀ X)) (T : Set (π₀ Y)) (n : SimplexCategoryᵒᵖ)
    (q : ((componentUnion X S : SSet.{u}) ⨯ (componentUnion Y T : SSet.{u})).obj n) :
    ((componentUnionProductIso X Y S T).inv.app n q).val =
      (prod.map (componentUnion X S).ι (componentUnion Y T).ι).app n q := by
  exact congrArg (fun a => a.app n q) (componentUnionProductIso_inv_ι X Y S T)

/-- Product selection commutes with exact inverse images of the original pair of arrows. -/
theorem componentUnionProduct_preimage {X' Y' : SSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') (S : Set (π₀ X')) (T : Set (π₀ Y')) :
    componentUnionProductSelector X Y ((mapπ₀ f) ⁻¹' S) ((mapπ₀ g) ⁻¹' T) =
      (mapπ₀ (prod.map f g)) ⁻¹' componentUnionProductSelector X' Y' S T := by
  ext c
  simp only [componentUnionProductSelector, Set.mem_preimage, Set.mem_prod,
    piZeroProductEquiv_natural]

/-- With the actual selector identification, original restricted product maps commute. -/
theorem componentUnionProductIso_natural {X' Y' : SSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') (S : Set (π₀ X')) (T : Set (π₀ Y')) :
    (componentUnionProductIso X Y ((mapπ₀ f) ⁻¹' S) ((mapπ₀ g) ⁻¹' T)).hom ≫
        prod.map (componentUnionPreimageMap f S) (componentUnionPreimageMap g T) =
      (Subcomplex.eqToIso (congrArg (componentUnion (X ⨯ Y))
        (componentUnionProduct_preimage f g S T))).hom ≫
        componentUnionPreimageMap (prod.map f g) (componentUnionProductSelector X' Y' S T) ≫
          (componentUnionProductIso X' Y' S T).hom := by
  apply prod.hom_ext
  · apply (cancel_mono (componentUnion X' S).ι).mp
    simp only [Category.assoc, componentUnionPreimageMap_ι,
      componentUnionPreimageMap_ι_assoc, componentUnionProductIso_fst,
      componentUnionProductIso_fst_assoc, Subcomplex.eqToIso_hom,
      Subcomplex.homOfLE_ι_assoc, prod.map_fst]
  · apply (cancel_mono (componentUnion Y' T).ι).mp
    simp only [Category.assoc, componentUnionPreimageMap_ι,
      componentUnionPreimageMap_ι_assoc, componentUnionProductIso_snd,
      componentUnionProductIso_snd_assoc, Subcomplex.eqToIso_hom,
      Subcomplex.homOfLE_ι_assoc, prod.map_snd]

/-- Empty/full selectors keep the literal empty/full product subcomplexes. -/
theorem componentUnionProductSelector_empty_univ (X Y : SSet.{u}) :
    componentUnionProductSelector X Y ∅ Set.univ = ∅ ∧
      componentUnionProductSelector X Y Set.univ ∅ = ∅ ∧
      componentUnionProductSelector X Y Set.univ Set.univ = Set.univ := by
  simp only [componentUnionProductSelector, Set.empty_prod, Set.prod_empty,
    Set.univ_prod_univ, Set.preimage_empty, Set.preimage_univ, and_self]

/-- Canonical full-subcomplex identification of the original selected product. -/
def componentUnionProductUnivIso (X Y : SSet.{u}) :
    (componentUnion (X ⨯ Y) (componentUnionProductSelector X Y Set.univ Set.univ) : SSet.{u}) ≅
      X ⨯ Y :=
  Subcomplex.eqToIso (by
    rw [(componentUnionProductSelector_empty_univ X Y).2.2, componentUnion_univ]) ≪≫
      Subcomplex.topIso _

theorem componentUnionProductUnivIso_hom (X Y : SSet.{u}) :
    (componentUnionProductUnivIso X Y).hom =
      (componentUnion (X ⨯ Y) (componentUnionProductSelector X Y Set.univ Set.univ)).ι := by
  simp only [componentUnionProductUnivIso, Iso.trans_hom, Subcomplex.eqToIso_hom,
    Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]

/-- The full-selector comparison agrees with the actual original full-subcomplex identifications. -/
theorem componentUnionProductIso_univ (X Y : SSet.{u}) :
    (componentUnionProductIso X Y Set.univ Set.univ).hom ≫
        prod.map (componentUnionPreimageTargetUnivIso X).hom
          (componentUnionPreimageTargetUnivIso Y).hom =
      (componentUnionProductUnivIso X Y).hom := by
  rw [componentUnionPreimageTargetUnivIso_hom, componentUnionPreimageTargetUnivIso_hom,
    componentUnionProductUnivIso_hom, componentUnionProductIso_hom_ι]

/-- A chosen original pair of component classes gives the exact inverse singleton selector. -/
theorem componentUnionProductSelector_singleton (X Y : SSet.{u}) (c : π₀ X) (d : π₀ Y) :
    componentUnionProductSelector X Y {c} {d} = {(piZeroProductEquiv X Y).symm (c, d)} := by
  ext a
  change (piZeroProductEquiv X Y a).1 = c ∧ (piZeroProductEquiv X Y a).2 = d ↔
    a = (piZeroProductEquiv X Y).symm (c, d)
  rw [← Prod.mk.injEq]
  exact (Equiv.eq_symm_apply (piZeroProductEquiv X Y)).symm

/-- The actual component of an original pair is canonically the product of its two components. -/
def componentProductIso (X Y : SSet.{u}) (c : π₀ X) (d : π₀ Y) :
    (π₀.component ((piZeroProductEquiv X Y).symm (c, d)) : SSet.{u}) ≅
      (π₀.component c : SSet.{u}) ⨯ (π₀.component d : SSet.{u}) := by
  have h : componentUnion (X ⨯ Y) (componentUnionProductSelector X Y {c} {d}) =
      π₀.component ((piZeroProductEquiv X Y).symm (c, d)) := by
    rw [componentUnionProductSelector_singleton, componentUnion_singleton]
  exact (Subcomplex.eqToIso h).symm ≪≫ componentUnionProductIso X Y {c} {d} ≪≫
    prod.mapIso (Subcomplex.eqToIso (componentUnion_singleton X c))
      (Subcomplex.eqToIso (componentUnion_singleton Y d))

@[reassoc (attr := simp)]
theorem componentProductIso_fst (X Y : SSet.{u}) (c : π₀ X) (d : π₀ Y) :
    (componentProductIso X Y c d).hom ≫ prod.fst ≫ (π₀.component c).ι =
      (π₀.component ((piZeroProductEquiv X Y).symm (c, d))).ι ≫ prod.fst := by
  simp only [componentProductIso, Iso.trans_hom, Iso.symm_hom,
    Subcomplex.eqToIso_hom, Subcomplex.eqToIso_inv, Category.assoc,
    prod.mapIso_hom, prod.map_fst_assoc, Subcomplex.homOfLE_ι,
    Subcomplex.homOfLE_ι_assoc, componentUnionProductIso_fst]

@[reassoc (attr := simp)]
theorem componentProductIso_snd (X Y : SSet.{u}) (c : π₀ X) (d : π₀ Y) :
    (componentProductIso X Y c d).hom ≫ prod.snd ≫ (π₀.component d).ι =
      (π₀.component ((piZeroProductEquiv X Y).symm (c, d))).ι ≫ prod.snd := by
  simp only [componentProductIso, Iso.trans_hom, Iso.symm_hom,
    Subcomplex.eqToIso_hom, Subcomplex.eqToIso_inv, Category.assoc,
    prod.mapIso_hom, prod.map_snd_assoc, Subcomplex.homOfLE_ι,
    Subcomplex.homOfLE_ι_assoc, componentUnionProductIso_snd]

@[reassoc (attr := simp)]
theorem componentProductIso_inv_ι (X Y : SSet.{u}) (c : π₀ X) (d : π₀ Y) :
    (componentProductIso X Y c d).inv ≫
        (π₀.component ((piZeroProductEquiv X Y).symm (c, d))).ι =
      prod.map (π₀.component c).ι (π₀.component d).ι := by
  apply (cancel_epi (componentProductIso X Y c d).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply prod.hom_ext
  · simpa only [Category.assoc, prod.map_fst] using (componentProductIso_fst X Y c d).symm
  · simpa only [Category.assoc, prod.map_snd] using (componentProductIso_snd X Y c d).symm

/-- The component of the actual original vertex pair, with no representative replacement. -/
def componentOriginalPairIso (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (π₀.component (π₀.mk (componentProductSimplex (op ⦋0⦌) x y)) : SSet.{u}) ≅
      (π₀.component (π₀.mk x) : SSet.{u}) ⨯ (π₀.component (π₀.mk y) : SSet.{u}) :=
  Subcomplex.eqToIso (congrArg π₀.component (piZeroProductEquiv_symm_mk x y).symm) ≪≫
    componentProductIso X Y (π₀.mk x) (π₀.mk y)

@[reassoc (attr := simp)]
theorem componentOriginalPairIso_fst (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (componentOriginalPairIso x y).hom ≫ prod.fst ≫ (π₀.component (π₀.mk x)).ι =
      (π₀.component (π₀.mk (componentProductSimplex (op ⦋0⦌) x y))).ι ≫ prod.fst := by
  simp only [componentOriginalPairIso, Iso.trans_hom, Category.assoc,
    componentProductIso_fst, Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι_assoc]

@[reassoc (attr := simp)]
theorem componentOriginalPairIso_snd (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (componentOriginalPairIso x y).hom ≫ prod.snd ≫ (π₀.component (π₀.mk y)).ι =
      (π₀.component (π₀.mk (componentProductSimplex (op ⦋0⦌) x y))).ι ≫ prod.snd := by
  simp only [componentOriginalPairIso, Iso.trans_hom, Category.assoc,
    componentProductIso_snd, Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι_assoc]

/-- Exact selected-source restriction of a genuine original Kan fibration. -/
theorem componentUnionPreimageMap_fibration (p : X ⟶ Y) [Fibration p] (T : Set (π₀ Y)) :
    Fibration (componentUnionPreimageMap p T) := by
  rw [modelCategoryQuillen.fibration_iff]
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := modelCategoryQuillen.J.rlp) (componentUnionPreimageMap_isPullback p T)
    ((modelCategoryQuillen.fibration_iff p).mp inferInstance)

private theorem selectedFiberOuterPullback (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    IsPullback
      ((Subcomplex.fiber (componentUnionPreimageMap p T) y).ι ≫
        (componentUnion X ((mapπ₀ p) ⁻¹' T)).ι)
      (IsTerminal.from stdSimplex.isTerminalObj₀
        (Subcomplex.fiber (componentUnionPreimageMap p T) y : SSet.{u}))
      p (SSet.const (X := Δ[0]) y.val) := by
  have hc : SSet.const (X := Δ[0]) y ≫ (componentUnion Y T).ι =
      SSet.const (X := Δ[0]) y.val := by rw [SSet.const_comp]; rfl
  rw [← hc]
  exact (Subcomplex.fiber_isPullback (componentUnionPreimageMap p T) y).paste_horiz
    (componentUnionPreimageMap_isPullback p T)

/-- The raw fibre comparison fixes the original target vertex and both original projections. -/
@[no_expose]
def componentUnionPreimageFiberIso (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    (Subcomplex.fiber (componentUnionPreimageMap p T) y : SSet.{u}) ≅
      (Subcomplex.fiber p y.val : SSet.{u}) := by
  exact (selectedFiberOuterPullback p T y).isoIsPullback _ _
    (Subcomplex.fiber_isPullback p y.val)

@[reassoc (attr := simp)]
theorem componentUnionPreimageFiberIso_hom_ι (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    (componentUnionPreimageFiberIso p T y).hom ≫ (Subcomplex.fiber p y.val).ι =
      (Subcomplex.fiber (componentUnionPreimageMap p T) y).ι ≫
        (componentUnion X ((mapπ₀ p) ⁻¹' T)).ι := by
  exact IsPullback.isoIsPullback_hom_fst X (Δ[0] : SSet.{u})
    (selectedFiberOuterPullback p T y) (Subcomplex.fiber_isPullback p y.val)

/-- The comparison hom is the actual native mapFiber of the original inclusion square. -/
theorem componentUnionPreimageFiberIso_hom (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    (componentUnionPreimageFiberIso p T y).hom =
      Subcomplex.mapFiber (componentUnion X ((mapπ₀ p) ⁻¹' T)).ι (componentUnion Y T).ι
        (componentUnionPreimageMap_ι p T).symm (y' := y.val) rfl := by
  apply (cancel_mono (Subcomplex.fiber p y.val).ι).mp
  rw [componentUnionPreimageFiberIso_hom_ι]
  exact (Subcomplex.mapFiber_ι (componentUnion X ((mapπ₀ p) ⁻¹' T)).ι
    (componentUnion Y T).ι (componentUnionPreimageMap_ι p T).symm
      (y' := y.val) rfl).symm

@[reassoc]
theorem componentUnionPreimageFiberIso_hom_base (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    (componentUnionPreimageFiberIso p T y).hom ≫
        IsTerminal.from stdSimplex.isTerminalObj₀ (Subcomplex.fiber p y.val : SSet.{u}) =
      IsTerminal.from stdSimplex.isTerminalObj₀
        (Subcomplex.fiber (componentUnionPreimageMap p T) y : SSet.{u}) := by
  exact IsPullback.isoIsPullback_hom_snd X (Δ[0] : SSet.{u})
    (selectedFiberOuterPullback p T y) (Subcomplex.fiber_isPullback p y.val)

@[reassoc (attr := simp)]
theorem componentUnionPreimageFiberIso_inv_ι (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    (componentUnionPreimageFiberIso p T y).inv ≫
        (Subcomplex.fiber (componentUnionPreimageMap p T) y).ι ≫
          (componentUnion X ((mapπ₀ p) ⁻¹' T)).ι = (Subcomplex.fiber p y.val).ι := by
  exact IsPullback.isoIsPullback_inv_fst X (Δ[0] : SSet.{u})
    (selectedFiberOuterPullback p T y) (Subcomplex.fiber_isPullback p y.val)

@[reassoc]
theorem componentUnionPreimageFiberIso_inv_base (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    (componentUnionPreimageFiberIso p T y).inv ≫
        IsTerminal.from stdSimplex.isTerminalObj₀
          (Subcomplex.fiber (componentUnionPreimageMap p T) y : SSet.{u}) =
      IsTerminal.from stdSimplex.isTerminalObj₀ (Subcomplex.fiber p y.val : SSet.{u}) := by
  exact IsPullback.isoIsPullback_inv_snd X (Δ[0] : SSet.{u})
    (selectedFiberOuterPullback p T y) (Subcomplex.fiber_isPullback p y.val)

/-- The actual factor of the original ambient fibre through the exact selected source. -/
def componentUnionPreimageFiberSourceMap (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    (Subcomplex.fiber p y.val : SSet.{u}) ⟶
      (componentUnion X ((mapπ₀ p) ⁻¹' T) : SSet.{u}) :=
  componentUnionPreimageLift p T (Subcomplex.fiber p y.val).ι (SSet.const y) (by
    rw [Subcomplex.fiber_ι_comp, SSet.const_comp]
    rfl)

@[reassoc (attr := simp)]
theorem componentUnionPreimageFiberSourceMap_ι (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    componentUnionPreimageFiberSourceMap p T y ≫
      (componentUnion X ((mapπ₀ p) ⁻¹' T)).ι = (Subcomplex.fiber p y.val).ι :=
  componentUnionPreimageLift_fst _ _ _ _ _

@[reassoc (attr := simp)]
theorem componentUnionPreimageFiberSourceMap_comp (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    componentUnionPreimageFiberSourceMap p T y ≫ componentUnionPreimageMap p T =
      SSet.const y := componentUnionPreimageLift_snd _ _ _ _ _

/-- The inverse comparison is the actual prescribed source factor of the original fibre. -/
theorem componentUnionPreimageFiberIso_inv_source (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    (componentUnionPreimageFiberIso p T y).inv ≫
        (Subcomplex.fiber (componentUnionPreimageMap p T) y).ι =
      componentUnionPreimageFiberSourceMap p T y := by
  apply (cancel_mono (componentUnion X ((mapπ₀ p) ⁻¹' T)).ι).mp
  rw [Category.assoc, componentUnionPreimageFiberIso_inv_ι,
    componentUnionPreimageFiberSourceMap_ι]

/-- All forward fibre simplices keep their original ambient value. -/
theorem componentUnionPreimageFiberIso_hom_val (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) (n : SimplexCategoryᵒᵖ)
    (q : (Subcomplex.fiber (componentUnionPreimageMap p T) y : SSet.{u}).obj n) :
    ((componentUnionPreimageFiberIso p T y).hom.app n q).val = q.val.val := by
  exact congrArg (fun a => a.app n q) (componentUnionPreimageFiberIso_hom_ι p T y)

/-- All inverse fibre simplices keep the same original ambient value. -/
theorem componentUnionPreimageFiberIso_inv_val (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) (n : SimplexCategoryᵒᵖ)
    (q : (Subcomplex.fiber p y.val : SSet.{u}).obj n) :
    ((componentUnionPreimageFiberIso p T y).inv.app n q).val.val = q.val := by
  exact congrArg (fun a => a.app n q) (componentUnionPreimageFiberIso_inv_ι p T y)

/-- Original points over the chosen target belong to the exact selected source. -/
def componentUnionPreimageFiberVertex (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) (x : X _⦋0⦌) (hx : p.app _ x = y.val) :
    (componentUnion X ((mapπ₀ p) ⁻¹' T) : SSet.{u}) _⦋0⦌ :=
  ⟨x, (mem_componentUnion_zero X _ x).mpr (by
    change mapπ₀ p (π₀.mk x) ∈ T
    rw [mapπ₀_mk, hx]
    exact (mem_componentUnion_zero Y T y.val).mp y.property)⟩

/-- The native selected-fibre point of the same original ambient lift. -/
def componentUnionPreimageFiberBasePoint (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) (x : X _⦋0⦌) (hx : p.app _ x = y.val) :
    (Subcomplex.fiber (componentUnionPreimageMap p T) y : SSet.{u}) _⦋0⦌ :=
  Subcomplex.fiber.basePoint (f := componentUnionPreimageMap p T)
    (componentUnionPreimageFiberVertex p T y x hx) (by
      apply Subtype.ext
      exact hx)

theorem componentUnionPreimageFiberIso_hom_basePoint (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) (x : X _⦋0⦌) (hx : p.app _ x = y.val) :
    (componentUnionPreimageFiberIso p T y).hom.app (op ⦋0⦌)
        (componentUnionPreimageFiberBasePoint p T y x hx) =
      Subcomplex.fiber.basePoint (f := p) x hx := by
  apply Subtype.ext
  exact componentUnionPreimageFiberIso_hom_val p T y _ _

theorem componentUnionPreimageFiberIso_inv_basePoint (p : X ⟶ Y) (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) (x : X _⦋0⦌) (hx : p.app _ x = y.val) :
    (componentUnionPreimageFiberIso p T y).inv.app (op ⦋0⦌)
        (Subcomplex.fiber.basePoint (f := p) x hx) =
      componentUnionPreimageFiberBasePoint p T y x hx := by
  apply Subtype.ext
  apply Subtype.ext
  exact componentUnionPreimageFiberIso_inv_val p T y _ _

/-- Exact source selection for an original commuting ambient square. -/
theorem componentUnionFiberSquare_selector {X' Y' : SSet.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ p' = p ≫ b) (T : Set (π₀ Y')) :
    (mapπ₀ p) ⁻¹' ((mapπ₀ b) ⁻¹' T) =
      (mapπ₀ a) ⁻¹' ((mapπ₀ p') ⁻¹' T) := by
  ext c
  change mapπ₀ b (mapπ₀ p c) ∈ T ↔ mapπ₀ p' (mapπ₀ a c) ∈ T
  rw [← mapπ₀_comp_apply, ← mapπ₀_comp_apply, h]

/-- The original ambient square acts on the exactly matched selected source. -/
def componentUnionFiberSquareSourceMap {X' Y' : SSet.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ p' = p ≫ b) (T : Set (π₀ Y')) :
    (componentUnion X ((mapπ₀ p) ⁻¹' ((mapπ₀ b) ⁻¹' T)) : SSet.{u}) ⟶
      (componentUnion X' ((mapπ₀ p') ⁻¹' T) : SSet.{u}) :=
  (Subcomplex.eqToIso (congrArg (componentUnion X)
    (componentUnionFiberSquare_selector p p' a b h T))).hom ≫
      componentUnionPreimageMap a ((mapπ₀ p') ⁻¹' T)

@[reassoc (attr := simp)]
theorem componentUnionFiberSquareSourceMap_ι {X' Y' : SSet.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ p' = p ≫ b) (T : Set (π₀ Y')) :
    componentUnionFiberSquareSourceMap p p' a b h T ≫
        (componentUnion X' ((mapπ₀ p') ⁻¹' T)).ι =
      (componentUnion X ((mapπ₀ p) ⁻¹' ((mapπ₀ b) ⁻¹' T))).ι ≫ a := by
  simp only [componentUnionFiberSquareSourceMap, Category.assoc,
    componentUnionPreimageMap_ι, Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι_assoc]

theorem componentUnionFiberSquare_comm {X' Y' : SSet.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ p' = p ≫ b) (T : Set (π₀ Y')) :
    componentUnionFiberSquareSourceMap p p' a b h T ≫ componentUnionPreimageMap p' T =
      componentUnionPreimageMap p ((mapπ₀ b) ⁻¹' T) ≫ componentUnionPreimageMap b T := by
  apply (cancel_mono (componentUnion Y' T).ι).mp
  simp only [Category.assoc, componentUnionPreimageMap_ι,
    componentUnionPreimageMap_ι_assoc, componentUnionFiberSquareSourceMap_ι_assoc]
  rw [h]

/-- The actual original target-vertex image, with no representative choice. -/
def componentUnionFiberSquareTargetVertex {Y' : SSet.{u}} (b : Y ⟶ Y') (T : Set (π₀ Y'))
    (y : (componentUnion Y ((mapπ₀ b) ⁻¹' T) : SSet.{u}) _⦋0⦌) :
    (componentUnion Y' T : SSet.{u}) _⦋0⦌ := (componentUnionPreimageMap b T).app _ y

/-- Canonical original fibre comparisons commute with the whole original ambient map square. -/
theorem componentUnionPreimageFiberIso_natural {X' Y' : SSet.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ p' = p ≫ b) (T : Set (π₀ Y'))
    (y : (componentUnion Y ((mapπ₀ b) ⁻¹' T) : SSet.{u}) _⦋0⦌) :
    (componentUnionPreimageFiberIso p ((mapπ₀ b) ⁻¹' T) y).hom ≫
        Subcomplex.mapFiber a b h
          (y := y.val)
          (y' := (componentUnionFiberSquareTargetVertex b T y).val)
          (componentUnionPreimageMap_app_val b T _ y).symm =
      Subcomplex.mapFiber (componentUnionFiberSquareSourceMap p p' a b h T)
        (componentUnionPreimageMap b T) (componentUnionFiberSquare_comm p p' a b h T)
        (y := y)
        (y' := componentUnionFiberSquareTargetVertex b T y) rfl ≫
          (componentUnionPreimageFiberIso p' T
              (componentUnionFiberSquareTargetVertex b T y)).hom := by
  apply (cancel_mono
    (Subcomplex.fiber p' (componentUnionFiberSquareTargetVertex b T y).val).ι).mp
  have ha := Subcomplex.mapFiber_ι a b h (y := y.val)
    (y' := (componentUnionFiberSquareTargetVertex b T y).val)
    (componentUnionPreimageMap_app_val b T _ y).symm
  have hs := Subcomplex.mapFiber_ι (componentUnionFiberSquareSourceMap p p' a b h T)
    (componentUnionPreimageMap b T) (componentUnionFiberSquare_comm p p' a b h T)
    (y := y) (y' := componentUnionFiberSquareTargetVertex b T y) rfl
  simp only [Category.assoc, ha, componentUnionPreimageFiberIso_hom_ι,
    componentUnionPreimageFiberIso_hom_ι_assoc]
  simpa only [Category.assoc, componentUnionFiberSquareSourceMap_ι] using
    (congrArg (fun f => f ≫ (componentUnion X' ((mapπ₀ p') ⁻¹' T)).ι) hs).symm

/-- Both actual fibres of a genuine fibration are Kan, without ambient Kan hypotheses. -/
theorem componentUnionPreimageFiberIso_kan (p : X ⟶ Y) [Fibration p] (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    KanComplex (Subcomplex.fiber (componentUnionPreimageMap p T) y : SSet.{u}) ∧
      KanComplex (Subcomplex.fiber p y.val : SSet.{u}) := by
  let _ : Fibration (componentUnionPreimageMap p T) := componentUnionPreimageMap_fibration p T
  exact ⟨inferInstance, inferInstance⟩

/-- The canonical actual fibre comparison has the full native weak predicate. -/
theorem componentUnionPreimageFiberIso_W (p : X ⟶ Y) [Fibration p] (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    KanComplex.W (componentUnionPreimageFiberIso p T y).hom := by
  let _ : KanComplex (Subcomplex.fiber (componentUnionPreimageMap p T) y : SSet.{u}) :=
    (componentUnionPreimageFiberIso_kan p T y).1
  let _ : KanComplex (Subcomplex.fiber p y.val : SSet.{u}) :=
    (componentUnionPreimageFiberIso_kan p T y).2
  exact KanComplex.W.ofIso (componentUnionPreimageFiberIso p T y)

/-- Every pointed map uses the actual selected source fibre point and its actual image. -/
theorem componentUnionPreimageFiberIso_bijective_piMap
    (p : X ⟶ Y) [Fibration p] (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) (n : ℕ)
    (q : (Subcomplex.fiber (componentUnionPreimageMap p T) y : SSet.{u}) _⦋0⦌) :
    Function.Bijective
      (KanComplex.π.map (componentUnionPreimageFiberIso p T y).hom rfl (n := n) (x := q)) :=
  (componentUnionPreimageFiberIso_W p T y).bijective_piMap n q

theorem componentUnionPreimageFiberIso_isEquivalence_mapFundamentalGroupoid
    (p : X ⟶ Y) [Fibration p] (T : Set (π₀ Y))
    (y : (componentUnion Y T : SSet.{u}) _⦋0⦌) :
    (SSet.mapFundamentalGroupoid (componentUnionPreimageFiberIso p T y).hom).IsEquivalence :=
  (componentUnionPreimageFiberIso_W p T y).isEquivalence_mapFundamentalGroupoid

/-- The inverse point equality is evaluated from the actual iso identity, not assumed
definitional. -/
theorem componentUnionPreimageFiberIso_hom_inv_point
    (p : X ⟶ Y) (T : Set (π₀ Y)) (y : (componentUnion Y T : SSet.{u}) _⦋0⦌)
    (q : (Subcomplex.fiber (componentUnionPreimageMap p T) y : SSet.{u}) _⦋0⦌) :
    (componentUnionPreimageFiberIso p T y).inv.app _
        ((componentUnionPreimageFiberIso p T y).hom.app _ q) = q := by
  exact congrArg (fun f => f.app (op ⦋0⦌) q) (componentUnionPreimageFiberIso p T y).hom_inv_id

theorem componentUnionPreimageFiberIso_inv_hom_point
    (p : X ⟶ Y) (T : Set (π₀ Y)) (y : (componentUnion Y T : SSet.{u}) _⦋0⦌)
    (q : (Subcomplex.fiber p y.val : SSet.{u}) _⦋0⦌) :
    (componentUnionPreimageFiberIso p T y).hom.app _
        ((componentUnionPreimageFiberIso p T y).inv.app _ q) = q := by
  exact congrArg (fun f => f.app (op ⦋0⦌) q) (componentUnionPreimageFiberIso p T y).inv_hom_id

/-- Every original pointed map is inverted with the genuine point transport. -/
theorem componentUnionPreimageFiberIso_piMap_leftInverse
    (p : X ⟶ Y) (T : Set (π₀ Y)) (y : (componentUnion Y T : SSet.{u}) _⦋0⦌)
    (n : ℕ) (q : (Subcomplex.fiber (componentUnionPreimageMap p T) y : SSet.{u}) _⦋0⦌)
    (v : KanComplex.π n (Subcomplex.fiber (componentUnionPreimageMap p T) y : SSet.{u}) q) :
    KanComplex.π.map (componentUnionPreimageFiberIso p T y).inv
        (componentUnionPreimageFiberIso_hom_inv_point p T y q) (n := n)
        (KanComplex.π.map (componentUnionPreimageFiberIso p T y).hom rfl (n := n)
            (x := q) v) = v := by
  have hp : ((componentUnionPreimageFiberIso p T y).hom ≫
      (componentUnionPreimageFiberIso p T y).inv).app _ q = q :=
    congrArg (fun f => f.app (op ⦋0⦌) q) (componentUnionPreimageFiberIso p T y).hom_inv_id
  have hm := KanComplex.π.map_comp_apply
    (componentUnionPreimageFiberIso p T y).hom (componentUnionPreimageFiberIso p T y).inv
    rfl (componentUnionPreimageFiberIso_hom_inv_point p T y q) hp v
  simpa only [(componentUnionPreimageFiberIso p T y).hom_inv_id,
    KanComplex.π.map_id_apply] using hm.symm

theorem componentUnionPreimageFiberIso_piMap_rightInverse
    (p : X ⟶ Y) (T : Set (π₀ Y)) (y : (componentUnion Y T : SSet.{u}) _⦋0⦌)
    (n : ℕ) (q : (Subcomplex.fiber p y.val : SSet.{u}) _⦋0⦌)
    (v : KanComplex.π n (Subcomplex.fiber p y.val : SSet.{u}) q) :
    KanComplex.π.map (componentUnionPreimageFiberIso p T y).hom
        (componentUnionPreimageFiberIso_inv_hom_point p T y q) (n := n)
        (KanComplex.π.map (componentUnionPreimageFiberIso p T y).inv rfl (n := n)
            (x := q) v) = v := by
  have hp : ((componentUnionPreimageFiberIso p T y).inv ≫
      (componentUnionPreimageFiberIso p T y).hom).app _ q = q :=
    congrArg (fun f => f.app (op ⦋0⦌) q) (componentUnionPreimageFiberIso p T y).inv_hom_id
  have hm := KanComplex.π.map_comp_apply
    (componentUnionPreimageFiberIso p T y).inv (componentUnionPreimageFiberIso p T y).hom
    rfl (componentUnionPreimageFiberIso_inv_hom_point p T y q) hp v
  simpa only [(componentUnionPreimageFiberIso p T y).inv_hom_id,
    KanComplex.π.map_id_apply] using hm.symm

end SSet
