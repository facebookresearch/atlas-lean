/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlagStage
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibration

/-!
# Reconstructing finite Stages from their zero row

For a finite Stage in the standard Waldhausen structure of an exact category,
every interval cell is canonically the cokernel of the corresponding map in
the zero row.  Consequently every natural transformation of zero-row chains
extends uniquely to a Stage morphism, and every zero-row natural isomorphism
extends canonically to a Stage natural isomorphism.

The extracted zero row is also an admissible-monomorphism flag.  Completing
that flag with `AdmissibleMonoFlag.toStage` recovers the original Stage up to
the canonical zero-row extension isomorphism.

This file constructs no Stage-fiber connectedness, contractibility,
realization weak equivalence, or Q/S comparison.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject
open CategoryTheory.ExactCategory

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance stageZeroRowWaldhausenCategory : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- The inclusion of the zero row in the finite Stage indexing category. -/
def zeroRowIndexFunctor (n : ℕ) : Fin (n + 1) ⥤ Ar n where
  obj j := interval 0 j (Fin.zero_le j)
  map f := Arrow.homMk' (𝟙 _) f (Subsingleton.elim _ _)
  map_id _ := by
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  map_comp _ _ := by
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _

/-- The canonical morphism between two nested finite intervals. -/
def intervalHomOfLE {n : ℕ}
    {i j i' j' : Fin (n + 1)}
    (hij : i ≤ j) (hi'j' : i' ≤ j')
    (hii' : i ≤ i') (hjj' : j ≤ j') :
    interval i j hij ⟶ interval i' j' hi'j' :=
  Arrow.homMk' (homOfLE hii') (homOfLE hjj') (Subsingleton.elim _ _)

/-- Every finite arrow object is its canonical interval presentation. -/
@[simp]
theorem interval_left_right_eq {n : ℕ} (I : Ar n) :
    interval I.left I.right (leOfHom I.hom) = I := by
  change Arrow.mk (homOfLE (leOfHom I.hom)) = I
  rw [Subsingleton.elim (homOfLE (leOfHom I.hom)) I.hom,
    Arrow.mk_eq]

/-- Normalize an arbitrary arrow object to the canonical interval with the
same endpoints. -/
def intervalNormalizationFunctor (n : ℕ) : Ar n ⥤ Ar n where
  obj I := interval I.left I.right (leOfHom I.hom)
  map {I J} f := intervalHomOfLE (leOfHom I.hom) (leOfHom J.hom)
    (leOfHom f.left) (leOfHom f.right)
  map_id _ := by
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  map_comp _ _ := by
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _

@[simp]
theorem intervalNormalizationFunctor_obj_interval {n : ℕ}
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (intervalNormalizationFunctor n).obj (interval i j hij) =
      interval i j hij :=
  rfl

/-- Canonical normalization of an interval object is naturally isomorphic to
the original arrow object. -/
def intervalNormalizationIso (n : ℕ) :
    intervalNormalizationFunctor n ≅ Functor.id (Ar n) :=
  NatIso.ofComponents
    (fun _ ↦ Arrow.isoMk (Iso.refl _) (Iso.refl _)
      (Subsingleton.elim _ _))
    (fun _ ↦ by
      apply Arrow.hom_ext <;> exact Subsingleton.elim _ _)

@[simp]
theorem intervalNormalizationIso_hom_app_interval {n : ℕ}
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (intervalNormalizationIso n).hom.app (interval i j hij) = 𝟙 _ := by
  apply Arrow.hom_ext <;> rfl

@[simp]
theorem intervalNormalizationIso_inv_app_interval {n : ℕ}
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (intervalNormalizationIso n).inv.app (interval i j hij) = 𝟙 _ := by
  apply Arrow.hom_ext <;> rfl

namespace Stage

variable {n : ℕ}

/-- The complete zero-row chain of a finite Stage. -/
def zeroRowChain (A : Stage C n) : ComposableArrows C n :=
  zeroRowIndexFunctor n ⋙ A.obj

@[simp]
theorem zeroRowChain_obj (A : Stage C n) (j : Fin (n + 1)) :
    A.zeroRowChain.obj j = A.zeroRowObj j :=
  rfl

@[simp]
theorem zeroRowChain_map (A : Stage C n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowChain.map (homOfLE hij) =
      A.obj.map (horiz (Fin.zero_le i) hij) :=
  rfl

/-- Every map from a zero-row object to the final zero-row object is an
admissible monomorphism. -/
theorem zeroRowChain_map_to_last_admissibleMono
    (A : Stage C n) (j : Fin (n + 1)) :
    IsAdmissibleMono
      (A.zeroRowChain.map (homOfLE (Fin.le_last j))) := by
  change IsAdmissibleMono
    (A.obj.map (horiz (Fin.zero_le j) (Fin.le_last j)))
  exact (A.property.cofiber_triple
    (Fin.zero_le j) (Fin.le_last j)).1

@[simp]
theorem zeroRowChain_map_succ (A : Stage C n) (i : Fin n) :
    A.zeroRowChain.map' i.val (i.val + 1)
      (Nat.le_succ i.val) (Nat.succ_le_iff.mpr i.isLt) =
      A.zeroRowSuccMap i := by
  rfl

/-- Restrict a Stage morphism to its zero-row chain. -/
def zeroRowHom {A B : Stage C n} (f : A ⟶ B) :
    A.zeroRowChain ⟶ B.zeroRowChain :=
  Functor.whiskerLeft (zeroRowIndexFunctor n) f.hom

@[simp]
theorem zeroRowHom_app {A B : Stage C n} (f : A ⟶ B)
    (j : Fin (n + 1)) :
    (A.zeroRowHom f).app j = A.zeroRowApp f j :=
  rfl

/-- The zero row of a finite Stage, with its inherited admissible-mono
successor maps. -/
def toAdmissibleMonoFlag (A : Stage C n) : AdmissibleMonoFlag C n where
  chain := A.zeroRowChain
  first_isZero := A.property.diag_isZero 0
  step_admissible i hi := by
    let r : Fin n := ⟨i, hi⟩
    change IsAdmissibleMono (A.zeroRowSuccMap r)
    exact (A.property.cofiber_triple (Fin.zero_le r.castSucc)
      r.castSucc_le_succ).1

@[simp]
theorem toAdmissibleMonoFlag_chain (A : Stage C n) :
    A.toAdmissibleMonoFlag.chain = A.zeroRowChain :=
  rfl

@[simp]
theorem toAdmissibleMonoFlag_chain_obj (A : Stage C n)
    (j : Fin (n + 1)) :
    A.toAdmissibleMonoFlag.chain.obj j = A.zeroRowObj j :=
  rfl

/-- The quotient projection from the right endpoint of a zero-row interval to
the corresponding Stage cell. -/
def zeroRowCellProjection (A : Stage C n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowChain.obj j ⟶ A.obj.obj (interval i j hij) :=
  A.obj.map (vert (Fin.zero_le i) hij)

/-- The zero-row interval map followed by the cell quotient projection is
zero. -/
@[reassoc (attr := simp)]
theorem zeroRowCell_comp_projection (A : Stage C n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowChain.map (homOfLE hij) ≫
      A.zeroRowCellProjection hij = 0 := by
  exact (A.property.cofiber_triple (Fin.zero_le i) hij).comp_eq_zero

/-- The zero-row interval and its Stage cell form an admissible exact
sequence. -/
theorem zeroRowCell_exact (A : Stage C n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsAdmissibleExact
      (ShortComplex.mk (A.zeroRowChain.map (homOfLE hij))
        (A.zeroRowCellProjection hij)
        (A.zeroRowCell_comp_projection hij)) := by
  exact ExactCategory.isAdmissibleExact_of_isCofibrationSequence
    (A.property.cofiber_triple (Fin.zero_le i) hij)

/-- Every Stage cell is canonically a cokernel of its zero-row interval map. -/
noncomputable def zeroRowCellIsColimit (A : Stage C n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsColimit (CokernelCofork.ofπ (A.zeroRowCellProjection hij)
      (A.zeroRowCell_comp_projection hij)) :=
  isColimit_cokernelCofork_of_isAdmissibleExact (A.zeroRowCell_exact hij)

/-- The cell quotient projection is an admissible epimorphism. -/
theorem zeroRowCellProjection_admissibleEpi (A : Stage C n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsAdmissibleEpi (A.zeroRowCellProjection hij) :=
  isAdmissibleEpi_g (A.zeroRowCell_exact hij)

/-- The projection to a cell in row zero is the identity. -/
@[simp]
theorem zeroRowCellProjection_zero (A : Stage C n)
    (j : Fin (n + 1)) :
    A.zeroRowCellProjection (Fin.zero_le j) = 𝟙 _ := by
  change A.obj.map (vert (Fin.zero_le (0 : Fin (n + 1)))
    (Fin.zero_le j)) = 𝟙 _
  rw [← A.obj.map_id]
  congr 1

/-- Projection to Stage cells is natural for every interval-map square. -/
@[reassoc]
theorem zeroRowCellProjection_naturality (A : Stage C n)
    {i j i' j' : Fin (n + 1)}
    (hij : i ≤ j) (hi'j' : i' ≤ j')
    (hii' : i ≤ i') (hjj' : j ≤ j') :
    A.zeroRowCellProjection hij ≫
        A.obj.map (intervalHomOfLE hij hi'j' hii' hjj') =
      A.zeroRowChain.map (homOfLE hjj') ≫
        A.zeroRowCellProjection hi'j' := by
  rw [A.zeroRowChain_map]
  change A.obj.map (vert (Fin.zero_le i) hij) ≫
      A.obj.map (intervalHomOfLE hij hi'j' hii' hjj') =
    A.obj.map (horiz (Fin.zero_le j) hjj') ≫
      A.obj.map (vert (Fin.zero_le i') hi'j')
  rw [← A.obj.map_comp, ← A.obj.map_comp]
  congr 1

/-- The canonical map on an interval cell induced by a natural transformation
of zero-row chains. -/
noncomputable def cellHomOfZeroRowHom {A B : Stage C n}
    (f : A.zeroRowChain ⟶ B.zeroRowChain)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.obj.obj (interval i j hij) ⟶
      B.obj.obj (interval i j hij) := by
  have hz : A.zeroRowChain.map (homOfLE hij) ≫
      (f.app j ≫ B.zeroRowCellProjection hij) = 0 := by
    rw [← Category.assoc, f.naturality, Category.assoc,
      B.zeroRowCell_comp_projection, comp_zero]
  exact (A.zeroRowCellIsColimit hij).desc
    (CokernelCofork.ofπ (f.app j ≫ B.zeroRowCellProjection hij) hz)

/-- The induced cell map is characterized by the two cokernel projections. -/
@[reassoc (attr := simp)]
theorem zeroRowCellProjection_cellHomOfZeroRowHom
    {A B : Stage C n} (f : A.zeroRowChain ⟶ B.zeroRowChain)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowCellProjection hij ≫ A.cellHomOfZeroRowHom f hij =
      f.app j ≫ B.zeroRowCellProjection hij := by
  exact Cofork.IsColimit.π_desc (A.zeroRowCellIsColimit hij)

/-- The induced cell maps are natural for every nested-interval morphism. -/
theorem cellHomOfZeroRowHom_naturality
    {A B : Stage C n} (f : A.zeroRowChain ⟶ B.zeroRowChain)
    {i j i' j' : Fin (n + 1)}
    (hij : i ≤ j) (hi'j' : i' ≤ j')
    (hii' : i ≤ i') (hjj' : j ≤ j') :
    A.obj.map (intervalHomOfLE hij hi'j' hii' hjj') ≫
        A.cellHomOfZeroRowHom f hi'j' =
      A.cellHomOfZeroRowHom f hij ≫
        B.obj.map (intervalHomOfLE hij hi'j' hii' hjj') := by
  let _ : Epi (A.zeroRowCellProjection hij) :=
    (A.zeroRowCellProjection_admissibleEpi hij).epi
  apply (cancel_epi (A.zeroRowCellProjection hij)).1
  calc
    A.zeroRowCellProjection hij ≫
        (A.obj.map (intervalHomOfLE hij hi'j' hii' hjj') ≫
          A.cellHomOfZeroRowHom f hi'j') =
      (A.zeroRowCellProjection hij ≫
        A.obj.map (intervalHomOfLE hij hi'j' hii' hjj')) ≫
          A.cellHomOfZeroRowHom f hi'j' :=
            (Category.assoc _ _ _).symm
    _ = (A.zeroRowChain.map (homOfLE hjj') ≫
        A.zeroRowCellProjection hi'j') ≫
          A.cellHomOfZeroRowHom f hi'j' := by
            rw [A.zeroRowCellProjection_naturality]
    _ = A.zeroRowChain.map (homOfLE hjj') ≫
        (A.zeroRowCellProjection hi'j' ≫
          A.cellHomOfZeroRowHom f hi'j') := Category.assoc _ _ _
    _ = A.zeroRowChain.map (homOfLE hjj') ≫
        (f.app j' ≫ B.zeroRowCellProjection hi'j') := by
          rw [A.zeroRowCellProjection_cellHomOfZeroRowHom]
    _ = (A.zeroRowChain.map (homOfLE hjj') ≫ f.app j') ≫
        B.zeroRowCellProjection hi'j' := (Category.assoc _ _ _).symm
    _ = (f.app j ≫ B.zeroRowChain.map (homOfLE hjj')) ≫
        B.zeroRowCellProjection hi'j' := by rw [f.naturality]
    _ = f.app j ≫
        (B.zeroRowChain.map (homOfLE hjj') ≫
          B.zeroRowCellProjection hi'j') := Category.assoc _ _ _
    _ = f.app j ≫
        (B.zeroRowCellProjection hij ≫
          B.obj.map (intervalHomOfLE hij hi'j' hii' hjj')) := by
            rw [B.zeroRowCellProjection_naturality]
    _ = (f.app j ≫ B.zeroRowCellProjection hij) ≫
        B.obj.map (intervalHomOfLE hij hi'j' hii' hjj') :=
          (Category.assoc _ _ _).symm
    _ = (A.zeroRowCellProjection hij ≫
        A.cellHomOfZeroRowHom f hij) ≫
          B.obj.map (intervalHomOfLE hij hi'j' hii' hjj') := by
            rw [A.zeroRowCellProjection_cellHomOfZeroRowHom]
    _ = A.zeroRowCellProjection hij ≫
        (A.cellHomOfZeroRowHom f hij ≫
          B.obj.map (intervalHomOfLE hij hi'j' hii' hjj')) :=
            Category.assoc _ _ _

/-- Cellwise extension over normalized interval objects. -/
noncomputable def normalizedCellHomOfZeroRowHom
    {A B : Stage C n} (f : A.zeroRowChain ⟶ B.zeroRowChain) :
    intervalNormalizationFunctor n ⋙ A.obj ⟶
      intervalNormalizationFunctor n ⋙ B.obj where
  app I := A.cellHomOfZeroRowHom f (leOfHom I.hom)
  naturality {I J} g := by
    exact A.cellHomOfZeroRowHom_naturality f
      (leOfHom I.hom) (leOfHom J.hom)
      (leOfHom g.left) (leOfHom g.right)

@[simp]
theorem normalizedCellHomOfZeroRowHom_app_interval
    {A B : Stage C n} (f : A.zeroRowChain ⟶ B.zeroRowChain)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (A.normalizedCellHomOfZeroRowHom f).app (interval i j hij) =
      A.cellHomOfZeroRowHom f hij := by
  change A.cellHomOfZeroRowHom f (leOfHom (homOfLE hij)) = _
  congr 1

/-- Normalizing interval objects does not change a Stage diagram. -/
def zeroRowNormalizationIso (A : Stage C n) :
    intervalNormalizationFunctor n ⋙ A.obj ≅ A.obj :=
  (Functor.isoWhiskerRight (intervalNormalizationIso n) A.obj).trans
    (Functor.leftUnitor A.obj)

@[simp]
theorem zeroRowNormalizationIso_hom_app_interval (A : Stage C n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowNormalizationIso.hom.app (interval i j hij) = 𝟙 _ := by
  simp [zeroRowNormalizationIso]

@[simp]
theorem zeroRowNormalizationIso_inv_app_interval (A : Stage C n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowNormalizationIso.inv.app (interval i j hij) = 𝟙 _ := by
  simp [zeroRowNormalizationIso]

/-- Extend a natural transformation of zero-row chains to the unique Stage
morphism with those zero-row components. -/
noncomputable def homOfZeroRowHom
    {A B : Stage C n} (f : A.zeroRowChain ⟶ B.zeroRowChain) : A ⟶ B := by
  refine ⟨(A.zeroRowNormalizationIso).inv ≫
    A.normalizedCellHomOfZeroRowHom f ≫
    B.zeroRowNormalizationIso.hom⟩

/-- The extended Stage morphism computes on every canonical interval as the
corresponding cokernel-induced cell map. -/
@[simp]
theorem homOfZeroRowHom_app_interval
    {A B : Stage C n} (f : A.zeroRowChain ⟶ B.zeroRowChain)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (A.homOfZeroRowHom f).hom.app (interval i j hij) =
      A.cellHomOfZeroRowHom f hij := by
  unfold homOfZeroRowHom
  change (A.zeroRowNormalizationIso.inv ≫
      A.normalizedCellHomOfZeroRowHom f ≫
        B.zeroRowNormalizationIso.hom).app (interval i j hij) = _
  rw [NatTrans.comp_app, NatTrans.comp_app]
  rw [A.zeroRowNormalizationIso_inv_app_interval,
    B.zeroRowNormalizationIso_hom_app_interval,
    A.normalizedCellHomOfZeroRowHom_app_interval]
  simp only [Functor.comp_obj, intervalNormalizationFunctor_obj_interval]
  rw [Category.id_comp, Category.comp_id]

/-- The extension has exactly the supplied components on the zero row. -/
@[simp]
theorem homOfZeroRowHom_app_zeroRow
    {A B : Stage C n} (f : A.zeroRowChain ⟶ B.zeroRowChain)
    (j : Fin (n + 1)) :
    (A.homOfZeroRowHom f).hom.app
        (interval 0 j (Fin.zero_le j)) = f.app j := by
  rw [A.homOfZeroRowHom_app_interval]
  have h := A.zeroRowCellProjection_cellHomOfZeroRowHom f
    (Fin.zero_le j)
  simpa only [A.zeroRowCellProjection_zero,
    B.zeroRowCellProjection_zero, zeroRowChain,
    zeroRowIndexFunctor, Functor.comp_obj,
    Category.id_comp, Category.comp_id] using h

/-- Restricting an extended zero-row morphism recovers the input morphism. -/
@[simp]
theorem zeroRowHom_homOfZeroRowHom
    {A B : Stage C n} (f : A.zeroRowChain ⟶ B.zeroRowChain) :
    A.zeroRowHom (A.homOfZeroRowHom f) = f := by
  ext j
  exact A.homOfZeroRowHom_app_zeroRow f j

/-- Cokernel extension of the restriction of a Stage morphism recovers each
interval component. -/
theorem cellHomOfZeroRowHom_zeroRowHom
    {A B : Stage C n} (f : A ⟶ B)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.cellHomOfZeroRowHom (A.zeroRowHom f) hij =
      f.hom.app (interval i j hij) := by
  let _ : Epi (A.zeroRowCellProjection hij) :=
    (A.zeroRowCellProjection_admissibleEpi hij).epi
  apply (cancel_epi (A.zeroRowCellProjection hij)).1
  rw [A.zeroRowCellProjection_cellHomOfZeroRowHom]
  exact (f.hom.naturality (vert (Fin.zero_le i) hij)).symm

/-- Extending the restriction of a Stage morphism recovers that morphism. -/
@[simp]
theorem homOfZeroRowHom_zeroRowHom
    {A B : Stage C n} (f : A ⟶ B) :
    A.homOfZeroRowHom (A.zeroRowHom f) = f := by
  apply ObjectProperty.hom_ext
  ext I
  rw [← interval_left_right_eq I]
  rw [A.homOfZeroRowHom_app_interval,
    A.cellHomOfZeroRowHom_zeroRowHom]

/-- Stage morphisms are equivalent to natural transformations of their
zero-row chains. -/
noncomputable def homEquivZeroRow (A B : Stage C n) :
    (A ⟶ B) ≃ (A.zeroRowChain ⟶ B.zeroRowChain) where
  toFun := A.zeroRowHom
  invFun := A.homOfZeroRowHom
  left_inv := A.homOfZeroRowHom_zeroRowHom
  right_inv := A.zeroRowHom_homOfZeroRowHom

/-- A morphism of finite Stages is determined by its component at the final
zero-row object.  Naturality recovers every earlier zero-row component by
cancelling the target's admissible-mono map to the final object. -/
theorem hom_ext_zeroRow_last
    {A B : Stage C n} {f g : A ⟶ B}
    (h : (A.zeroRowHom f).app (Fin.last n) =
      (A.zeroRowHom g).app (Fin.last n)) :
    f = g := by
  apply (A.homEquivZeroRow B).injective
  change A.zeroRowHom f = A.zeroRowHom g
  ext j
  let _ : Mono (B.zeroRowChain.map (homOfLE (Fin.le_last j))) :=
    (B.zeroRowChain_map_to_last_admissibleMono j).mono
  apply (cancel_mono
    (B.zeroRowChain.map (homOfLE (Fin.le_last j)))).1
  rw [← (A.zeroRowHom f).naturality,
    ← (A.zeroRowHom g).naturality, h]

@[simp]
theorem zeroRowHom_id (A : Stage C n) :
    A.zeroRowHom (𝟙 A) = 𝟙 A.zeroRowChain :=
  rfl

@[simp]
theorem zeroRowHom_comp {A B D : Stage C n}
    (f : A ⟶ B) (g : B ⟶ D) :
    A.zeroRowHom (f ≫ g) = A.zeroRowHom f ≫ B.zeroRowHom g :=
  rfl

@[simp]
theorem homOfZeroRowHom_id (A : Stage C n) :
    A.homOfZeroRowHom (𝟙 A.zeroRowChain) = 𝟙 A := by
  apply (A.homEquivZeroRow A).injective
  change A.zeroRowHom (A.homOfZeroRowHom (𝟙 A.zeroRowChain)) =
    A.zeroRowHom (𝟙 A)
  rw [A.zeroRowHom_homOfZeroRowHom, A.zeroRowHom_id]

@[simp]
theorem homOfZeroRowHom_comp
    {A B D : Stage C n}
    (f : A.zeroRowChain ⟶ B.zeroRowChain)
    (g : B.zeroRowChain ⟶ D.zeroRowChain) :
    A.homOfZeroRowHom (f ≫ g) =
      A.homOfZeroRowHom f ≫ B.homOfZeroRowHom g := by
  apply (A.homEquivZeroRow D).injective
  change A.zeroRowHom (A.homOfZeroRowHom (f ≫ g)) =
    A.zeroRowHom (A.homOfZeroRowHom f ≫ B.homOfZeroRowHom g)
  rw [A.zeroRowHom_homOfZeroRowHom, A.zeroRowHom_comp,
    A.zeroRowHom_homOfZeroRowHom, B.zeroRowHom_homOfZeroRowHom]

/-- Extend a natural isomorphism of zero-row chains to a Stage natural
isomorphism. -/
noncomputable def isoOfZeroRowIso {A B : Stage C n}
    (e : A.zeroRowChain ≅ B.zeroRowChain) : A ≅ B where
  hom := A.homOfZeroRowHom e.hom
  inv := B.homOfZeroRowHom e.inv
  hom_inv_id := by
    rw [← A.homOfZeroRowHom_comp, e.hom_inv_id,
      A.homOfZeroRowHom_id]
  inv_hom_id := by
    rw [← B.homOfZeroRowHom_comp, e.inv_hom_id,
      B.homOfZeroRowHom_id]

@[simp]
theorem isoOfZeroRowIso_hom_app_interval {A B : Stage C n}
    (e : A.zeroRowChain ≅ B.zeroRowChain)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (A.isoOfZeroRowIso e).hom.hom.app (interval i j hij) =
      A.cellHomOfZeroRowHom e.hom hij :=
  A.homOfZeroRowHom_app_interval e.hom hij

@[simp]
theorem isoOfZeroRowIso_inv_app_interval {A B : Stage C n}
    (e : A.zeroRowChain ≅ B.zeroRowChain)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (A.isoOfZeroRowIso e).inv.hom.app (interval i j hij) =
      B.cellHomOfZeroRowHom e.inv hij :=
  B.homOfZeroRowHom_app_interval e.inv hij

@[simp]
theorem isoOfZeroRowIso_hom_app_zeroRow {A B : Stage C n}
    (e : A.zeroRowChain ≅ B.zeroRowChain)
    (j : Fin (n + 1)) :
    (A.isoOfZeroRowIso e).hom.hom.app
      (interval 0 j (Fin.zero_le j)) = e.hom.app j :=
  A.homOfZeroRowHom_app_zeroRow e.hom j

@[simp]
theorem isoOfZeroRowIso_inv_app_zeroRow {A B : Stage C n}
    (e : A.zeroRowChain ≅ B.zeroRowChain)
    (j : Fin (n + 1)) :
    (A.isoOfZeroRowIso e).inv.hom.app
      (interval 0 j (Fin.zero_le j)) = e.inv.app j :=
  B.homOfZeroRowHom_app_zeroRow e.inv j

/-- Restrict a Stage isomorphism to its zero-row chains. -/
def zeroRowIsoOfIso {A B : Stage C n} (e : A ≅ B) :
    A.zeroRowChain ≅ B.zeroRowChain where
  hom := A.zeroRowHom e.hom
  inv := B.zeroRowHom e.inv
  hom_inv_id := by rw [← A.zeroRowHom_comp, e.hom_inv_id, A.zeroRowHom_id]
  inv_hom_id := by rw [← B.zeroRowHom_comp, e.inv_hom_id, B.zeroRowHom_id]

@[simp]
theorem zeroRowIsoOfIso_isoOfZeroRowIso {A B : Stage C n}
    (e : A.zeroRowChain ≅ B.zeroRowChain) :
    zeroRowIsoOfIso (A.isoOfZeroRowIso e) = e := by
  apply Iso.ext
  exact A.zeroRowHom_homOfZeroRowHom e.hom

@[simp]
theorem isoOfZeroRowIso_zeroRowIsoOfIso {A B : Stage C n}
    (e : A ≅ B) :
    A.isoOfZeroRowIso (zeroRowIsoOfIso e) = e := by
  apply Iso.ext
  exact A.homOfZeroRowHom_zeroRowHom e.hom

@[simp]
theorem isoOfZeroRowIso_refl (A : Stage C n) :
    A.isoOfZeroRowIso (Iso.refl A.zeroRowChain) = Iso.refl A := by
  apply Iso.ext
  exact A.homOfZeroRowHom_id

@[simp]
theorem isoOfZeroRowIso_trans {A B D : Stage C n}
    (e : A.zeroRowChain ≅ B.zeroRowChain)
    (f : B.zeroRowChain ≅ D.zeroRowChain) :
    A.isoOfZeroRowIso (e.trans f) =
      (A.isoOfZeroRowIso e).trans (B.isoOfZeroRowIso f) := by
  apply Iso.ext
  exact A.homOfZeroRowHom_comp e.hom f.hom

@[simp]
theorem isoOfZeroRowIso_symm {A B : Stage C n}
    (e : A.zeroRowChain ≅ B.zeroRowChain) :
    B.isoOfZeroRowIso e.symm = (A.isoOfZeroRowIso e).symm := by
  apply Iso.ext
  rfl

end Stage

namespace AdmissibleMonoFlag

variable {n : ℕ}

/-- The original admissible flag is naturally isomorphic to the zero row of
its quotient-completed Stage. -/
noncomputable def zeroRowNatIso (F : AdmissibleMonoFlag C n) :
    F.chain ≅ F.toStage.zeroRowChain :=
  NatIso.ofComponents (fun j ↦ F.zeroRowIso j) (fun {i j} g ↦ by
    let hij := leOfHom g
    change F.chain.map g ≫
        F.intervalπ 0 j (Fin.zero_le j) =
      F.intervalπ 0 i (Fin.zero_le i) ≫
        F.intervalMap (Fin.zero_le i) (Fin.zero_le j) le_rfl hij
    have h := (F.intervalπ_naturality
      (Fin.zero_le i) (Fin.zero_le j) le_rfl hij).symm
    rw [Subsingleton.elim (homOfLE hij) g] at h
    exact h)

@[simp]
theorem zeroRowNatIso_hom_app (F : AdmissibleMonoFlag C n)
    (j : Fin (n + 1)) :
    (F.zeroRowNatIso).hom.app j = F.intervalπ 0 j (Fin.zero_le j) :=
  rfl

@[simp]
theorem zeroRowNatIso_inv_app (F : AdmissibleMonoFlag C n)
    (j : Fin (n + 1)) :
    (F.zeroRowNatIso).inv.app j = (F.zeroRowIso j).inv :=
  rfl

end AdmissibleMonoFlag

namespace Stage

variable {n : ℕ}

/-- Reconstructing a Stage from its extracted admissible zero-row flag gives
the original Stage up to the canonical zero-row extension isomorphism. -/
noncomputable def toAdmissibleMonoFlagToStageIso (A : Stage C n) :
    A ≅ A.toAdmissibleMonoFlag.toStage :=
  A.isoOfZeroRowIso A.toAdmissibleMonoFlag.zeroRowNatIso

@[simp]
theorem toAdmissibleMonoFlagToStageIso_hom_app_zeroRow
    (A : Stage C n) (j : Fin (n + 1)) :
    A.toAdmissibleMonoFlagToStageIso.hom.hom.app
        (interval 0 j (Fin.zero_le j)) =
      A.toAdmissibleMonoFlag.intervalπ 0 j (Fin.zero_le j) := by
  exact A.isoOfZeroRowIso_hom_app_zeroRow
    A.toAdmissibleMonoFlag.zeroRowNatIso j

@[simp]
theorem toAdmissibleMonoFlagToStageIso_hom_app_interval
    (A : Stage C n) {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.toAdmissibleMonoFlagToStageIso.hom.hom.app
        (interval i j hij) =
      A.cellHomOfZeroRowHom
        A.toAdmissibleMonoFlag.zeroRowNatIso.hom hij :=
  A.isoOfZeroRowIso_hom_app_interval
    A.toAdmissibleMonoFlag.zeroRowNatIso hij

/-- Characteristic quotient formula for reconstruction through
`AdmissibleMonoFlag.toStage`. -/
@[reassoc]
theorem zeroRowCellProjection_toAdmissibleMonoFlagToStageIso_hom_app
    (A : Stage C n) {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowCellProjection hij ≫
        A.toAdmissibleMonoFlagToStageIso.hom.hom.app
          (interval i j hij) =
      A.toAdmissibleMonoFlag.zeroRowNatIso.hom.app j ≫
        A.toAdmissibleMonoFlag.toStage.zeroRowCellProjection hij := by
  rw [A.toAdmissibleMonoFlagToStageIso_hom_app_interval]
  exact A.zeroRowCellProjection_cellHomOfZeroRowHom
    A.toAdmissibleMonoFlag.zeroRowNatIso.hom hij

end Stage

end CategoryTheory.Waldhausen.SConstruction

end
