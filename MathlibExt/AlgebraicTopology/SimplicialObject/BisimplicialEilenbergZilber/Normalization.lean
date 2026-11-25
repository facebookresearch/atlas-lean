/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.TotalHomotopy
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlternating
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialMap
public import MathlibExt.AlgebraicTopology.DoldKan.HomotopyNaturality
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies

/-!
# Double normalization of a bisimplicial alternating total complex

The horizontal and vertical Dold--Kan projectors define commuting bicomplex
endomorphisms.  Their total maps compose to a double-normalization projector
which is naturally homotopic to the identity.  The file also records the
bidegree projector, its idempotence, and the two degeneracy-vanishing lemmas
used by the projected shuffle/Alexander--Whitney calculation.
-/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialNormalization

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasFiniteCoproducts A]
  (B : SimplicialObject (SimplicialObject A))

/-- Dold--Kan normalization in the outer simplicial direction. -/
noncomputable def outerPInfty :
    AlgebraicTopology.bisimplicialAlternatingBicomplex A B ⟶
      AlgebraicTopology.bisimplicialAlternatingBicomplex A B :=
  ((AlgebraicTopology.alternatingFaceMapComplex A).mapHomologicalComplex
    (ComplexShape.down ℕ)).map
      (AlgebraicTopology.DoldKan.PInfty :
        (AlgebraicTopology.alternatingFaceMapComplex (SimplicialObject A)).obj B ⟶ _)

/-- Dold--Kan normalization in the inner simplicial direction. -/
noncomputable def verticalPInfty :
    AlgebraicTopology.bisimplicialAlternatingBicomplex A B ⟶
      AlgebraicTopology.bisimplicialAlternatingBicomplex A B :=
  (NatTrans.mapHomologicalComplex
    (AlgebraicTopology.DoldKan.natTransPInfty A)
    (ComplexShape.down ℕ)).app
      ((AlgebraicTopology.alternatingFaceMapComplex (SimplicialObject A)).obj B)

omit [Limits.HasFiniteCoproducts A] in
@[simp]
theorem outerPInfty_f_f (p q : ℕ) :
    ((outerPInfty B).f p).f q =
      ((AlgebraicTopology.DoldKan.PInfty :
        (AlgebraicTopology.alternatingFaceMapComplex (SimplicialObject A)).obj B ⟶ _).f p).app
          (Opposite.op ⦋q⦌) := rfl

omit [Limits.HasFiniteCoproducts A] in
@[simp]
theorem verticalPInfty_f_f (p q : ℕ) :
    ((verticalPInfty B).f p).f q =
      (AlgebraicTopology.DoldKan.PInfty :
        (AlgebraicTopology.alternatingFaceMapComplex A).obj
          (B.obj (Opposite.op ⦋p⦌)) ⟶ _).f q := rfl

omit [Limits.HasFiniteCoproducts A] in
/-- The two bicomplex normalization projectors commute. -/
theorem outerPInfty_comp_verticalPInfty :
    outerPInfty B ≫ verticalPInfty B =
      verticalPInfty B ≫ outerPInfty B := by
  ext p q
  change ((AlgebraicTopology.DoldKan.PInfty :
      (AlgebraicTopology.alternatingFaceMapComplex (SimplicialObject A)).obj B ⟶ _).f p).app
        (Opposite.op ⦋q⦌) ≫
      (AlgebraicTopology.DoldKan.PInfty :
        (AlgebraicTopology.alternatingFaceMapComplex A).obj
          (B.obj (Opposite.op ⦋p⦌)) ⟶ _).f q = _
  exact AlgebraicTopology.DoldKan.PInfty_f_naturality q
    ((AlgebraicTopology.DoldKan.PInfty :
      (AlgebraicTopology.alternatingFaceMapComplex (SimplicialObject A)).obj B ⟶ _).f p)

omit [Limits.HasFiniteCoproducts A] in
/-- A noninjective outer simplex map is killed by the target outer projector. -/
theorem map_comp_outerPInfty_eq_zero_of_not_mono
    (p q r t : ℕ) (α : ⦋r⦌ ⟶ ⦋p⦌) (β : ⦋t⦌ ⟶ ⦋q⦌)
    (hα : ¬ Mono α) :
    AlgebraicTopology.Bisimplicial.map B α β ≫
        ((outerPInfty B).f r).f t = 0 := by
  have hzero := AlgebraicTopology.DoldKan.degeneracy_comp_PInfty B r α hα
  have hzeroApp := congrArg (fun k => k.app (Opposite.op ⦋q⦌)) hzero
  have hzeroApp' :
      (B.map α.op).app (Opposite.op ⦋q⦌) ≫
        ((AlgebraicTopology.DoldKan.PInfty :
          (AlgebraicTopology.alternatingFaceMapComplex (SimplicialObject A)).obj B ⟶ _).f r).app
            (Opposite.op ⦋q⦌) = 0 := by
    simpa only [NatTrans.comp_app, zero_app] using hzeroApp
  have hnat :=
    ((AlgebraicTopology.DoldKan.PInfty :
      (AlgebraicTopology.alternatingFaceMapComplex
        (SimplicialObject A)).obj B ⟶ _).f r).naturality β.op
  change (B.obj (Opposite.op ⦋r⦌)).map β.op ≫
      ((AlgebraicTopology.DoldKan.PInfty :
        (AlgebraicTopology.alternatingFaceMapComplex (SimplicialObject A)).obj B ⟶ _).f r).app
          (Opposite.op ⦋t⦌) =
    ((AlgebraicTopology.DoldKan.PInfty :
      (AlgebraicTopology.alternatingFaceMapComplex (SimplicialObject A)).obj B ⟶ _).f r).app
        (Opposite.op ⦋q⦌) ≫
      (B.obj (Opposite.op ⦋r⦌)).map β.op at hnat
  unfold AlgebraicTopology.Bisimplicial.map
  rw [outerPInfty_f_f]
  rw [Category.assoc]
  change (B.map α.op).app (Opposite.op ⦋q⦌) ≫
      (B.obj (Opposite.op ⦋r⦌)).map β.op ≫
        ((AlgebraicTopology.DoldKan.PInfty :
          (AlgebraicTopology.alternatingFaceMapComplex (SimplicialObject A)).obj B ⟶ _).f r).app
            (Opposite.op ⦋t⦌) = 0
  calc
    _ = (B.map α.op).app (Opposite.op ⦋q⦌) ≫
        (((AlgebraicTopology.DoldKan.PInfty :
          (AlgebraicTopology.alternatingFaceMapComplex (SimplicialObject A)).obj B ⟶ _).f r).app
            (Opposite.op ⦋q⦌) ≫
          (B.obj (Opposite.op ⦋r⦌)).map β.op) := by
      rw [hnat]
    _ = ((B.map α.op).app (Opposite.op ⦋q⦌) ≫
        ((AlgebraicTopology.DoldKan.PInfty :
          (AlgebraicTopology.alternatingFaceMapComplex (SimplicialObject A)).obj B ⟶ _).f r).app
            (Opposite.op ⦋q⦌)) ≫
          (B.obj (Opposite.op ⦋r⦌)).map β.op := by rw [Category.assoc]
    _ = 0 := by rw [hzeroApp', CategoryTheory.Limits.zero_comp]

omit [Limits.HasFiniteCoproducts A] in
/-- A noninjective inner simplex map is killed by the target inner projector. -/
theorem map_comp_verticalPInfty_eq_zero_of_not_mono
    (p q r t : ℕ) (α : ⦋r⦌ ⟶ ⦋p⦌) (β : ⦋t⦌ ⟶ ⦋q⦌)
    (hβ : ¬ Mono β) :
    AlgebraicTopology.Bisimplicial.map B α β ≫
        ((verticalPInfty B).f r).f t = 0 := by
  have hzero := AlgebraicTopology.DoldKan.degeneracy_comp_PInfty
    (B.obj (Opposite.op ⦋r⦌)) t β hβ
  unfold AlgebraicTopology.Bisimplicial.map
  rw [verticalPInfty_f_f]
  rw [Category.assoc]
  change (B.map α.op).app (Opposite.op ⦋q⦌) ≫
      (B.obj (Opposite.op ⦋r⦌)).map β.op ≫
        (AlgebraicTopology.DoldKan.PInfty :
          (AlgebraicTopology.alternatingFaceMapComplex A).obj
            (B.obj (Opposite.op ⦋r⦌)) ⟶ _).f t = 0
  rw [hzero, CategoryTheory.Limits.comp_zero]

/-- The outer projector is homotopic to the bicomplex identity. -/
noncomputable def outerHomotopy :
    Homotopy (outerPInfty B)
      (𝟙 (AlgebraicTopology.bisimplicialAlternatingBicomplex A B)) := by
  let H := (AlgebraicTopology.alternatingFaceMapComplex A).mapHomotopy
    (AlgebraicTopology.DoldKan.homotopyPInftyToId B)
  change Homotopy
    (((AlgebraicTopology.alternatingFaceMapComplex A).mapHomologicalComplex
      (ComplexShape.down ℕ)).map AlgebraicTopology.DoldKan.PInfty)
    (𝟙 (((AlgebraicTopology.alternatingFaceMapComplex A).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        ((AlgebraicTopology.alternatingFaceMapComplex (SimplicialObject A)).obj B)))
  exact H

/-- The flipped vertical projector is homotopic to the flipped identity. -/
noncomputable def verticalFlipHomotopy :
    Homotopy
      (HomologicalComplex₂.flipMap (verticalPInfty B))
      (HomologicalComplex₂.flipMap
        (𝟙 (AlgebraicTopology.bisimplicialAlternatingBicomplex A B))) where
  hom q q' :=
    { f := fun p =>
        (AlgebraicTopology.DoldKan.homotopyPInftyToId
          (B.obj (Opposite.op ⦋p⦌))).hom q q'
      comm' := by
        intro p p' _
        let d := ((AlgebraicTopology.alternatingFaceMapComplex
          (SimplicialObject A)).obj B).d p p'
        exact AlgebraicTopology.DoldKan.homotopyPInftyToId_hom_naturality
          q q' d }
  zero q q' hrel := by
    ext p
    exact (AlgebraicTopology.DoldKan.homotopyPInftyToId
      (B.obj (Opposite.op ⦋p⦌))).zero q q' hrel
  comm q := by
    ext p
    exact (AlgebraicTopology.DoldKan.homotopyPInftyToId
      (B.obj (Opposite.op ⦋p⦌))).comm q

noncomputable def outerTotalPInfty :
    AlgebraicTopology.bisimplicialAlternatingTotalComplex A B ⟶
      AlgebraicTopology.bisimplicialAlternatingTotalComplex A B :=
  HomologicalComplex₂.total.map (outerPInfty B) (ComplexShape.down ℕ)

noncomputable def verticalTotalPInfty :
    AlgebraicTopology.bisimplicialAlternatingTotalComplex A B ⟶
      AlgebraicTopology.bisimplicialAlternatingTotalComplex A B :=
  HomologicalComplex₂.total.map (verticalPInfty B) (ComplexShape.down ℕ)

noncomputable def outerTotalHomotopy :
    Homotopy (outerTotalPInfty B)
      (𝟙 (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B)) := by
  change Homotopy
    (HomologicalComplex₂.total.map (outerPInfty B) (ComplexShape.down ℕ))
    (𝟙 ((AlgebraicTopology.bisimplicialAlternatingBicomplex A B).total
      (ComplexShape.down ℕ)))
  let H := HomologicalComplex₂.totalMapHomotopy₁
    (outerHomotopy B) (ComplexShape.down ℕ)
  exact H.trans (Homotopy.ofEq (by simp))

noncomputable def verticalTotalHomotopy :
    Homotopy (verticalTotalPInfty B)
      (𝟙 (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B)) := by
  change Homotopy
    (HomologicalComplex₂.total.map (verticalPInfty B) (ComplexShape.down ℕ))
    (𝟙 ((AlgebraicTopology.bisimplicialAlternatingBicomplex A B).total
      (ComplexShape.down ℕ)))
  let H := HomologicalComplex₂.totalMapHomotopy₂
    (ComplexShape.down ℕ) (verticalFlipHomotopy B)
  exact H.trans (Homotopy.ofEq (by simp))

/-- The double-normalization projector on the total complex. -/
noncomputable def totalPInfty :
    AlgebraicTopology.bisimplicialAlternatingTotalComplex A B ⟶
      AlgebraicTopology.bisimplicialAlternatingTotalComplex A B :=
  outerTotalPInfty B ≫ verticalTotalPInfty B

/-- The double-normalization total projector is homotopic to the identity. -/
noncomputable def totalPInftyHomotopy :
    Homotopy (totalPInfty B)
      (𝟙 (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B)) := by
  let H := (outerTotalHomotopy B).compRight (verticalTotalPInfty B)
  exact H.trans ((Homotopy.ofEq (by simp)).trans (verticalTotalHomotopy B))

/-- The double-normalization projector on one bidegree object. -/
noncomputable def bidegreePInfty (p q : ℕ) :
    (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  ((outerPInfty B).f p).f q ≫ ((verticalPInfty B).f p).f q

omit [Limits.HasFiniteCoproducts A] in
/-- The bidegree double-normalization projector is idempotent. -/
theorem bidegreePInfty_idem (p q : ℕ) :
    bidegreePInfty B p q ≫ bidegreePInfty B p q =
      bidegreePInfty B p q := by
  let O := ((outerPInfty B).f p).f q
  let V := ((verticalPInfty B).f p).f q
  have hcomm : O ≫ V = V ≫ O := by
    exact congrArg (fun k => (k.f p).f q)
      (outerPInfty_comp_verticalPInfty B)
  have hO : O ≫ O = O := by
    dsimp only [O]
    exact congrArg
      (fun k : B.obj (Opposite.op ⦋p⦌) ⟶ B.obj (Opposite.op ⦋p⦌) =>
        k.app (Opposite.op ⦋q⦌))
      (AlgebraicTopology.DoldKan.PInfty_f_idem p)
  have hV : V ≫ V = V := by
    dsimp only [V]
    exact AlgebraicTopology.DoldKan.PInfty_f_idem q
  change (O ≫ V) ≫ (O ≫ V) = O ≫ V
  calc
    _ = O ≫ (V ≫ O) ≫ V := by simp only [Category.assoc]
    _ = O ≫ (O ≫ V) ≫ V := by rw [← hcomm]
    _ = _ := by
      rw [Category.assoc O V V, hV]
      rw [← Category.assoc O O V, hO]

@[reassoc]
theorem totalι_comp_totalPInfty (p q n : ℕ) (h : p + q = n) :
    (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
        (ComplexShape.down ℕ) p q n h ≫ (totalPInfty B).f n =
      bidegreePInfty B p q ≫
        (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
          (ComplexShape.down ℕ) p q n h := by
  unfold totalPInfty outerTotalPInfty verticalTotalPInfty bidegreePInfty
  rw [HomologicalComplex.comp_f,
    HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ιTotal_map]
  rw [Category.assoc]

end AlgebraicTopology.BisimplicialNormalization
