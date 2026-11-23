/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.SubcomplexModelCofibration
public import Mathlib.Topology.Homotopy.TopCat.Basic
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
public import MathlibExt.Topology.Homotopy.UnderSourceInverse

/-!
# Based Whitehead for spaces with specified based classical CW models

The literal zero-cell inclusions make the pointed CW models cofibrant in the
existing Under model category. The shared source-under weak-inverse factory
supplies the based inverse by its PUnit/constant-map specialization. Both
complete inverse families are restricted from their actual source images
to the original singleton points.

The final construction transports these families through the supplied based
CW model maps. It retains the original forward map and places Hausdorffness
and classical CW assumptions only on the models.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology
open scoped TopCat.modelCategory

universe u

namespace Topology.CWComplex

namespace BasedWhiteheadConstruction

private abbrev pointObject : TopCat.{u} := TopCat.of PUnit.{u + 1}

private def zeroSubcomplex (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
    (x : X) (j : cell (Set.univ : Set X) 0) (hj : map 0 j ![] = x) :
    Subcomplex (Set.univ : Set X) := by
  let J : (n : ℕ) → Set (cell (Set.univ : Set X) n)
    | 0 => {j}
    | n + 1 => ∅
  refine { carrier := {x}, I := J, closed' := isClosed_singleton, union' := ?_ }
  rw [Set.empty_union]
  ext z
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, k, hk⟩
    cases n with
    | zero =>
      have hkj : k.val = j := Set.mem_singleton_iff.mp k.property
      have hz : z ∈ openCell 0 j := by simpa only [hkj] using hk
      rw [openCell_zero_eq_singleton] at hz
      exact (Set.mem_singleton_iff.mp hz).trans hj
    | succ n => exact (Set.notMem_empty _ k.property).elim
  · intro hz
    subst z
    refine ⟨0, ⟨j, Set.mem_singleton j⟩, ?_⟩
    rw [openCell_zero_eq_singleton, hj]
    exact Set.mem_singleton x

private theorem zeroPoint_cofibration (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (x : X) (j : cell (Set.univ : Set X) 0)
    (hj : map 0 j ![] = x) :
    Cofibration (TopCat.const x : pointObject.{u} ⟶ X) := by
  let A := zeroSubcomplex X x j hj
  let h : pointObject.{u} ≃ₜ (A : Set X) :=
    { toFun := fun _ => ⟨x, Set.mem_singleton x⟩
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun z => Subtype.ext
        (Set.mem_singleton_iff.mp z.property).symm
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const }
  let e : pointObject.{u} ≅ TopCat.of (A : Set X) := TopCat.isoOfHomeo h
  have he : (TopCat.const x : pointObject.{u} ⟶ X) = e.hom ≫ subcomplexInclusion A := by
    apply TopCat.ext
    intro z
    rfl
  rw [cofibration_iff, he]
  change TopCat.realizedBoundaryInclusions.rlp.llp (e.hom ≫ subcomplexInclusion A)
  exact (TopCat.realizedBoundaryInclusions.rlp.llp).comp_mem e.hom (subcomplexInclusion A)
    (MorphismProperty.llp_of_isIso _ e.hom)
    (subcomplexInclusion_mem_realizedBoundaryLLP X A)

private theorem literalPointCofibrantBasedInverse
    (X Y : TopCat.{u}) (x : X) (y : Y)
    [Cofibration (TopCat.const x : pointObject.{u} ⟶ X)]
    [Cofibration (TopCat.const y : pointObject.{u} ⟶ Y)]
    (f : X ⟶ Y) (hxy : f x = y) (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ g : Y ⟶ X, g y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (f ≫ g).hom (𝟙 X : X ⟶ X).hom {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (g ≫ f).hom (𝟙 Y : Y ⟶ Y).hom {y}) := by
  let i : pointObject.{u} ⟶ X := TopCat.const x
  let j : pointObject.{u} ⟶ Y := TopCat.const y
  have hSource : i ≫ f = j := by
    apply TopCat.ext
    intro z
    exact hxy
  let R := TopCat.sourceRelativeInverseOfWeak i j f hSource hf
  have hg : R.inverse y = x := ConcreteCategory.congr_hom R.inverse_source PUnit.unit
  let HL : ContinuousMap.HomotopyRel (f ≫ R.inverse).hom
      (𝟙 X : X ⟶ X).hom {x} :=
    { toHomotopy := R.leftHomotopy.toHomotopy
      prop' := by
        intro t z hz
        have hz' : z = x := Set.mem_singleton_iff.mp hz
        subst z
        exact R.leftHomotopy.eq_fst t ⟨PUnit.unit, rfl⟩ }
  let HR : ContinuousMap.HomotopyRel (R.inverse ≫ f).hom
      (𝟙 Y : Y ⟶ Y).hom {y} :=
    { toHomotopy := R.rightHomotopy.toHomotopy
      prop' := by
        intro t z hz
        have hz' : z = y := Set.mem_singleton_iff.mp hz
        subst z
        exact R.rightHomotopy.eq_fst t ⟨PUnit.unit, rfl⟩ }
  exact ⟨R.inverse, hg, ⟨HL⟩, ⟨HR⟩⟩

private theorem literalCWBasedInverse
    (X Y : TopCat.{u}) [T2Space X] [T2Space Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (x : X) (y : Y) (jx : cell (Set.univ : Set X) 0) (jy : cell (Set.univ : Set Y) 0)
    (hjx : map 0 jx ![] = x) (hjy : map 0 jy ![] = y)
    (f : X ⟶ Y) (hxy : f x = y) (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ g : Y ⟶ X, g y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (f ≫ g).hom (𝟙 X : X ⟶ X).hom {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (g ≫ f).hom (𝟙 Y : Y ⟶ Y).hom {y}) := by
  letI : Cofibration (TopCat.const x : pointObject.{u} ⟶ X) :=
    zeroPoint_cofibration X x jx hjx
  letI : Cofibration (TopCat.const y : pointObject.{u} ⟶ Y) :=
    zeroPoint_cofibration Y y jy hjy
  exact literalPointCofibrantBasedInverse X Y x y f hxy hf

end BasedWhiteheadConstruction

/-- A weak map between actual spaces with specified based Hausdorff classical
CW models has an inverse and both continuous point-relative homotopies. The
CW and Hausdorff assumptions concern the models; the original forward map is
the given `f`. -/
theorem basedCWTypeWhitehead
    (X Y CX CY : TopCat.{u}) [T2Space CX] [T2Space CY]
    [CWComplex (Set.univ : Set CX)] [CWComplex (Set.univ : Set CY)]
    (x : X) (y : Y) (cx : CX) (cy : CY)
    (jx : cell (Set.univ : Set CX) 0) (jy : cell (Set.univ : Set CY) 0)
    (hjx : map 0 jx ![] = cx) (hjy : map 0 jy ![] = cy)
    (rx : X ⟶ CX) (sx : CX ⟶ X) (ry : Y ⟶ CY) (sy : CY ⟶ Y)
    (hrx : rx x = cx) (hsx : sx cx = x) (hry : ry y = cy) (hsy : sy cy = y)
    (LX : ContinuousMap.HomotopyRel (rx ≫ sx).hom (𝟙 X : X ⟶ X).hom {x})
    (RX : ContinuousMap.HomotopyRel (sx ≫ rx).hom (𝟙 CX : CX ⟶ CX).hom {cx})
    (LY : ContinuousMap.HomotopyRel (ry ≫ sy).hom (𝟙 Y : Y ⟶ Y).hom {y})
    (RY : ContinuousMap.HomotopyRel (sy ≫ ry).hom (𝟙 CY : CY ⟶ CY).hom {cy})
    (f : X ⟶ Y) (hxy : f x = y) (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ g : Y ⟶ X, g y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (f ≫ g).hom (𝟙 X : X ⟶ X).hom {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (g ≫ f).hom (𝟙 Y : Y ⟶ Y).hom {y}) := by
  let ex : ContinuousMap.HomotopyEquiv X CX :=
    { toFun := rx.hom
      invFun := sx.hom
      left_inv := ⟨LX.toHomotopy⟩
      right_inv := ⟨RX.toHomotopy⟩ }
  let ey : ContinuousMap.HomotopyEquiv Y CY :=
    { toFun := ry.hom
      invFun := sy.hom
      left_inv := ⟨LY.toHomotopy⟩
      right_inv := ⟨RY.toHomotopy⟩ }
  let F : CX ⟶ CY := sx ≫ f ≫ ry
  have hF : F cx = cy := by
    change ry (f (sx cx)) = cy
    rw [hsx, hxy, hry]
  have hFW : TopCat.weakHomotopyEquivalences F :=
    TopCat.weakHomotopyEquivalences.comp_mem sx (f ≫ ry)
      (TopCat.homotopyEquiv_invFun_mem ex)
      (TopCat.weakHomotopyEquivalences.comp_mem f ry hf (TopCat.homotopyEquiv_toFun_mem ey))
  obtain ⟨k, hk, ⟨HKX⟩, ⟨HKY⟩⟩ :=
    BasedWhiteheadConstruction.literalCWBasedInverse CX CY cx cy jx jy hjx hjy F hF hFW
  let g : Y ⟶ X := ry ≫ k ≫ sx
  have hg : g y = x := by
    change sx (k (ry y)) = x
    rw [hry, hk, hsx]
  let A₁ : ContinuousMap.HomotopyRel (f ≫ g).hom
      (rx ≫ F ≫ k ≫ sx).hom {x} :=
    (LX.symm.compContinuousMap (f ≫ g).hom).cast rfl rfl
  let B₁ := HKX.compContinuousMap sx.hom
  let A₂ : ContinuousMap.HomotopyRel (rx ≫ F ≫ k ≫ sx).hom (rx ≫ sx).hom {x} :=
    { toHomotopy := B₁.toHomotopy.compContinuousMap rx.hom
      prop' := by
        intro t z hz
        have hz' : z = x := Set.mem_singleton_iff.mp hz
        subst z
        exact B₁.eq_fst t (by
          change rx x ∈ {cx}
          rw [hrx]
          exact Set.mem_singleton cx) }
  let HLeft : ContinuousMap.HomotopyRel (f ≫ g).hom (𝟙 X : X ⟶ X).hom {x} :=
    (A₁.trans A₂).trans LX
  have hfg : (g ≫ f) y = y := by
    change f (g y) = y
    rw [hg, hxy]
  let A₃ : ContinuousMap.HomotopyRel (g ≫ f).hom
      (ry ≫ k ≫ F ≫ sy).hom {y} :=
    { toHomotopy := LY.symm.toHomotopy.compContinuousMap (g ≫ f).hom
      prop' := by
        intro t z hz
        have hz' : z = y := Set.mem_singleton_iff.mp hz
        subst z
        exact LY.symm.eq_fst t (by
          change (g ≫ f) y ∈ {y}
          rw [hfg]
          exact Set.mem_singleton y) }
  let B₂ := HKY.compContinuousMap sy.hom
  let A₄ : ContinuousMap.HomotopyRel (ry ≫ k ≫ F ≫ sy).hom (ry ≫ sy).hom {y} :=
    { toHomotopy := B₂.toHomotopy.compContinuousMap ry.hom
      prop' := by
        intro t z hz
        have hz' : z = y := Set.mem_singleton_iff.mp hz
        subst z
        change sy (HKY (t, ry y)) = sy (F (k (ry y)))
        rw [hry]
        calc
          sy (HKY (t, cy)) = sy cy :=
            congrArg sy (HKY.eq_snd t (Set.mem_singleton cy))
          _ = y := hsy
          _ = sy (F (k cy)) := by rw [hk, hF, hsy] }
  let HRight : ContinuousMap.HomotopyRel (g ≫ f).hom (𝟙 Y : Y ⟶ Y).hom {y} :=
    (A₃.trans A₄).trans LY
  exact ⟨g, hg, ⟨HLeft⟩, ⟨HRight⟩⟩

end Topology.CWComplex

namespace TopCat

/-- A literal weak based map between spaces with genuine cofibrant point
inclusions has an actual based inverse and BOTH singleton-relative inverse
families. The existing Under model category, all-space fibrancy and actual
compact-open path-object conversion are reused; CW/model or inverse witnesses
are not supplied. -/
public theorem exists_based_inverse_of_weak_of_cofibrant_points
    (X Y : TopCat.{u}) (x : X) (y : Y)
    [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    [Cofibration (TopCat.const y : TopCat.of PUnit.{u + 1} ⟶ Y)]
    (f : X ⟶ Y) (hxy : f x = y) (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ g : Y ⟶ X, g y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (f ≫ g).hom (𝟙 X : X ⟶ X).hom {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (g ≫ f).hom (𝟙 Y : Y ⟶ Y).hom {y}) := by
  exact Topology.CWComplex.BasedWhiteheadConstruction.literalPointCofibrantBasedInverse
    X Y x y f hxy hf

end TopCat

end
