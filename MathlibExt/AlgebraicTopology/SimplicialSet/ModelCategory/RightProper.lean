/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ExInfinity
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import MathlibExt.AlgebraicTopology.ModelCategory.Proper
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SubdivisionAnodyne
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import Mathlib.AlgebraicTopology.ModelCategory.Opposite
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Right properness of the Kan–Quillen model structure

The actual Ex∞ tower preserves finite limits and simplicial fibrations.
Its weak unit then reduces the pullback weak-equivalence property to the
fibrant-object theorem in the opposite model category. No right-properness
or homotopy-cartesian gluing premise is supplied.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet

private abbrev exIter : ℕ → SSet.{u} ⥤ SSet.{u} :=
  Nat.rec (𝟭 _) (fun _ F => F ⋙ SSet.ex)

private abbrev exTower (X : SSet.{u}) : ℕ ⥤ SSet.{u} :=
  Functor.ofSequence (fun n => exUnit.app ((exIter n).obj X))

private theorem exTower_map_succ (X : SSet.{u}) (n : ℕ) :
    (exTower X).map (homOfLE (n.le_add_right 1)) =
      exUnit.app ((exIter n).obj X) :=
  Functor.ofSequence_map_homOfLE_succ _ n

private theorem exIter_succ_map {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (exIter (n + 1)).map f = SSet.ex.map ((exIter n).map f) := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private abbrev exTowerFunctor : SSet.{u} ⥤ (ℕ ⥤ SSet.{u}) where
  obj := exTower
  map {X Y} f := NatTrans.ofSequence
    (fun n => (exIter n).map f) (fun n => by
      rw [exTower_map_succ, exTower_map_succ, exIter_succ_map]
      simpa only [Functor.id_map] using (exUnit.naturality ((exIter n).map f)).symm)
  map_id X := by
    apply NatTrans.ext
    funext n
    exact (exIter n).map_id X
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact (exIter n).map_comp f g

private theorem exInfinity_eq_towerColimit :
    (SSet.exInfinity : SSet.{u} ⥤ SSet.{u}) =
      exTowerFunctor.{u} ⋙ (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}) := by
  rfl

private instance exIter_preservesFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (exIter.{u} n) := by
  induction n with
  | zero => change PreservesFiniteLimits (𝟭 SSet.{u}); infer_instance
  | succ n ih =>
      change PreservesFiniteLimits (exIter n ⋙ SSet.ex)
      let _ : PreservesFiniteLimits (exIter n) := ih
      infer_instance

private instance exTowerFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (exTowerFunctor : SSet.{u} ⥤ (ℕ ⥤ SSet.{u})) :=
  preservesFiniteLimits_of_evaluation _ (fun n => by
    change PreservesFiniteLimits (exIter n)
    infer_instance)

private instance simplicialFilteredColim_preservesFiniteLimits :
    PreservesFiniteLimits (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}) where
  preservesFiniteLimits J _ _ := by infer_instance

/-- The actual infinite Ex construction preserves finite limits, including pullbacks. -/
instance exInfinity_preservesFiniteLimits :
    PreservesFiniteLimits (SSet.exInfinity : SSet.{u} ⥤ SSet.{u}) := by
  rw [exInfinity_eq_towerColimit]
  infer_instance

private theorem fibration_colimitMap_of_filtered
    {F G : ℕ ⥤ SSet.{u}} (φ : F ⟶ G) (hφ : ∀ n, Fibration (φ.app n)) :
    Fibration (colim.map φ) := by
  rw [modelCategoryQuillen.fibration_iff]
  intro A B g hg
  simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hg
  obtain ⟨n, ⟨i⟩⟩ := hg
  constructor
  intro a b sq
  let _ : Fact (Cardinal.aleph0.{u}.IsRegular) := ⟨Cardinal.isRegular_aleph0⟩
  let _ : IsCardinalFiltered ℕ Cardinal.aleph0.{u} := by
    rw [isCardinalFiltered_aleph0_iff]
    infer_instance
  let _ : IsFinitelyPresentable.{u} (horn.{u} (n + 1) i : SSet.{u}) := inferInstance
  let _ : IsFinitelyPresentable.{u} (Δ[n + 1] : SSet.{u}) := inferInstance
  obtain ⟨j, a', ha'⟩ := IsCardinalPresentable.exists_hom_of_isColimit
    Cardinal.aleph0.{u} (colimit.isColimit F) a
  obtain ⟨k, b', hb'⟩ := IsCardinalPresentable.exists_hom_of_isColimit
    Cardinal.aleph0.{u} (colimit.isColimit G) b
  change a' ≫ colimit.ι F j = a at ha'
  change b' ≫ colimit.ι G k = b at hb'
  have heq : (a' ≫ φ.app j) ≫ colimit.ι G j =
      ((horn.{u} (n + 1) i).ι ≫ b') ≫ colimit.ι G k := by
    calc
      (a' ≫ φ.app j) ≫ colimit.ι G j = a' ≫ colimit.ι F j ≫ colim.map φ := by
        simp only [Category.assoc, colimit.ι_map]
      _ = a ≫ colim.map φ := by rw [← Category.assoc, ha']
      _ = (horn.{u} (n + 1) i).ι ≫ b := sq.w
      _ = ((horn.{u} (n + 1) i).ι ≫ b') ≫ colimit.ι G k := by
        rw [Category.assoc, hb']
  obtain ⟨l, u, v, huv⟩ := IsCardinalPresentable.exists_eq_of_isColimit
    Cardinal.aleph0.{u} (colimit.isColimit G) (a' ≫ φ.app j)
      ((horn.{u} (n + 1) i).ι ≫ b') heq
  let _ : Fibration (φ.app l) := hφ l
  have sq' : CommSq (a' ≫ F.map u) (horn.{u} (n + 1) i).ι (φ.app l) (b' ≫ G.map v) := by
    constructor
    rw [Category.assoc, φ.naturality, ← Category.assoc, huv, Category.assoc]
  exact CommSq.HasLift.mk'
    { l := sq'.lift ≫ colimit.ι F l
      fac_left := by
        rw [← Category.assoc, sq'.fac_left, Category.assoc, colimit.w, ha']
      fac_right := by
        rw [Category.assoc, colimit.ι_map, ← Category.assoc, sq'.fac_right,
          Category.assoc, colimit.w, hb'] }

private theorem exIter_map_fibration {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] (n : ℕ) :
    Fibration ((exIter n).map p) := by
  induction n with
  | zero => exact inferInstanceAs (Fibration p)
  | succ n ih =>
      change Fibration (SSet.ex.map ((exIter n).map p))
      let _ : Fibration ((exIter n).map p) := ih
      exact instFibrationExMap _

namespace modelCategoryQuillen

/-- Ex∞ sends each actual simplicial fibration to a simplicial fibration. -/
scoped instance instFibrationExInfinityMap {E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] : Fibration (SSet.exInfinity.map p) := by
  rw [exInfinity_eq_towerColimit]
  exact fibration_colimitMap_of_filtered (exTowerFunctor.map p)
    (fun n => exIter_map_fibration p n)

end modelCategoryQuillen

private theorem exInfinity_map_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    realizationWeakEquivalences (SSet.exInfinity.map f) ↔ realizationWeakEquivalences f := by
  have hx := exInfinityUnit_mem_realizationWeakEquivalences X
  have hy := exInfinityUnit_mem_realizationWeakEquivalences Y
  have comm : f ≫ exInfinityUnit.app Y = exInfinityUnit.app X ≫ SSet.exInfinity.map f := by
    simpa only [Functor.id_map] using exInfinityUnit.naturality f
  constructor
  · intro hf
    have hc := realizationWeakEquivalences.comp_mem _ _ hx hf
    rw [← comm] at hc
    exact realizationWeakEquivalences.of_postcomp _ _ hy hc
  · intro hf
    have hc := realizationWeakEquivalences.comp_mem _ _ hf hy
    rw [comm] at hc
    exact realizationWeakEquivalences.of_precomp _ _ hx hc

private theorem cofibrant_op_of_kan (X : SSet.{u}) [KanComplex X] : IsCofibrant (op X) := by
  apply (isCofibrant_iff_of_isInitial (terminal.from X).op terminalIsTerminal.op).mpr
  rw [cofibration_op_iff]
  exact inferInstanceAs (IsFibrant X)

private theorem weak_of_pullback_of_kan
    {A B X Y : SSet.{u}} {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) [Fibration p] [WeakEquivalence f]
    [KanComplex B] [KanComplex Y] : WeakEquivalence f' := by
  let _ : IsCofibrant (op B) := cofibrant_op_of_kan B
  let _ : IsCofibrant (op Y) := cofibrant_op_of_kan Y
  let _ : Cofibration p.op := by rw [cofibration_op_iff]; infer_instance
  let _ : WeakEquivalence f.op := by rw [weakEquivalences_op_iff]; infer_instance
  exact (weakEquivalences_op_iff _).mp
    (weakEquivalence_of_isPushout_of_cofibrant sq.op)

namespace modelCategoryQuillen

/-- The selected Kan–Quillen model structure is right proper in every value universe. -/
scoped instance instIsRightProper : IsRightProper SSet.{u} where
  weakEquivalences_isStableUnderBaseChangeAgainst_fibrations := by
    constructor
    intro X Y p hp
    constructor
    intro A B p' f' f sq hf
    let _ : Fibration p := (HomotopicalAlgebra.fibration_iff _).mpr hp
    let _ : Fibration (SSet.exInfinity.map p) := instFibrationExInfinityMap p
    have hfEx : realizationWeakEquivalences (SSet.exInfinity.map f) :=
      (exInfinity_map_weak_iff f).mpr hf
    let _ : WeakEquivalence (SSet.exInfinity.map f) :=
      (HomotopicalAlgebra.weakEquivalence_iff _).mpr hfEx
    let _ : KanComplex (SSet.exInfinity.obj A) := SSet.exInfinity_kanComplex A
    let _ : KanComplex (SSet.exInfinity.obj Y) := SSet.exInfinity_kanComplex Y
    have hw : WeakEquivalence (SSet.exInfinity.map f') :=
      weak_of_pullback_of_kan (sq.map SSet.exInfinity)
    exact (exInfinity_map_weak_iff f').mp
      ((HomotopicalAlgebra.weakEquivalence_iff _).mp hw)

end modelCategoryQuillen

end SSet

end
