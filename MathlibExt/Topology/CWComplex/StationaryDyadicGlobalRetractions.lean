/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.CommonDimensionUnion
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.CategoryTheory.Functor.OfSequence
import MathlibExt.Topology.Category.TopCat.QuotientPushout
import MathlibExt.Topology.Category.TopCat.BinaryClosedGlue
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.CompactOpen
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Stationary dyadic global common-space retractions

Construct both actual end retractions and ordinary whole-end relative homotopies.
The local collapse outputs, exact dyadic tail formula, every-stage laws and shared
original zero points belong to the same returned package. The public constructor
derives every output from the original Hausdorff classical CW space.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
open scoped unitInterval

universe u

namespace ActualStationaryFixedEndTower

section PushoutDescent

variable {D A B P Z : TopCat.{u}} {f : D ⟶ A} {g : D ⟶ B}
  {i : A ⟶ P} {j : B ⟶ P}

private def actualPushoutDesc (h : IsPushout f g i j)
    (a : A ⟶ Z) (b : B ⟶ Z) (hab : f ≫ a = g ≫ b) : P ⟶ Z :=
  h.isoPushout.hom ≫ pushout.desc a b hab

private theorem actualPushoutDesc_left (h : IsPushout f g i j)
    (a : A ⟶ Z) (b : B ⟶ Z) (hab : f ≫ a = g ≫ b) (x : A) :
    actualPushoutDesc h a b hab (i x) = a x := by
  have he : h.isoPushout.hom (i x) = pushout.inl f g x :=
    ConcreteCategory.congr_hom h.inl_isoPushout_hom x
  exact (congrArg (pushout.desc a b hab) he).trans
    (ConcreteCategory.congr_hom (pushout.inl_desc a b hab) x)

private theorem actualPushoutDesc_right (h : IsPushout f g i j)
    (a : A ⟶ Z) (b : B ⟶ Z) (hab : f ≫ a = g ≫ b) (x : B) :
    actualPushoutDesc h a b hab (j x) = b x := by
  have he : h.isoPushout.hom (j x) = pushout.inr f g x :=
    ConcreteCategory.congr_hom h.inr_isoPushout_hom x
  exact (congrArg (pushout.desc a b hab) he).trans
    (ConcreteCategory.congr_hom (pushout.inr_desc a b hab) x)

private def actualPushoutHomotopy (h : IsPushout f g i j)
    {a₀ a₁ : A ⟶ Z} {b₀ b₁ : B ⟶ Z}
    (HA : TopCat.Homotopy a₀ a₁) (HB : TopCat.Homotopy b₀ b₁)
    (h₀ : f ≫ a₀ = g ≫ b₀) (h₁ : f ≫ a₁ = g ≫ b₁)
    (hw : ∀ t : unitInterval, ∀ d : D, HA (t, f d) = HB (t, g d)) :
    TopCat.Homotopy (actualPushoutDesc h a₀ b₀ h₀)
      (actualPushoutDesc h a₁ b₁ h₁) :=
  (TopCat.Homotopy.pushoutDesc HA HB h₀ h₁ hw).compContinuousMap
    h.isoPushout.hom.hom

private theorem actualPushoutHomotopy_left (h : IsPushout f g i j)
    {a₀ a₁ : A ⟶ Z} {b₀ b₁ : B ⟶ Z}
    (HA : TopCat.Homotopy a₀ a₁) (HB : TopCat.Homotopy b₀ b₁)
    (h₀ : f ≫ a₀ = g ≫ b₀) (h₁ : f ≫ a₁ = g ≫ b₁)
    (hw : ∀ t : unitInterval, ∀ d : D, HA (t, f d) = HB (t, g d))
    (t : unitInterval) (x : A) :
    actualPushoutHomotopy h HA HB h₀ h₁ hw (t, i x) = HA (t, x) := by
  have he : h.isoPushout.hom (i x) = pushout.inl f g x :=
    ConcreteCategory.congr_hom h.inl_isoPushout_hom x
  exact (congrArg (fun p => TopCat.Homotopy.pushoutDesc HA HB h₀ h₁ hw (t, p)) he).trans
    (TopCat.Homotopy.pushoutDesc_apply_inl HA HB h₀ h₁ hw t x)

private theorem actualPushoutHomotopy_right (h : IsPushout f g i j)
    {a₀ a₁ : A ⟶ Z} {b₀ b₁ : B ⟶ Z}
    (HA : TopCat.Homotopy a₀ a₁) (HB : TopCat.Homotopy b₀ b₁)
    (h₀ : f ≫ a₀ = g ≫ b₀) (h₁ : f ≫ a₁ = g ≫ b₁)
    (hw : ∀ t : unitInterval, ∀ d : D, HA (t, f d) = HB (t, g d))
    (t : unitInterval) (x : B) :
    actualPushoutHomotopy h HA HB h₀ h₁ hw (t, j x) = HB (t, x) := by
  have he : h.isoPushout.hom (j x) = pushout.inr f g x :=
    ConcreteCategory.congr_hom h.inr_isoPushout_hom x
  exact (congrArg (fun p => TopCat.Homotopy.pushoutDesc HA HB h₀ h₁ hw (t, p)) he).trans
    (TopCat.Homotopy.pushoutDesc_apply_inr HA HB h₀ h₁ hw t x)

end PushoutDescent

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private abbrev system := Topology.CWComplex.commonSuccessorSystem X
private abbrev stage (n : ℕ) : TopCat.{u} := ((system X).stages n).space

private theorem intermediateRetraction_square (n : ℕ) :
    TopCat.ofHom ((system X).stages n).polyhedral ≫ 𝟙 (stage X n) =
      TopCat.ofHom ((system X).familyOld n) ≫
        TopCat.ofHom (((system X).stages n).polyhedral.comp ((system X).familyRetraction n)) := by
  apply TopCat.ext
  intro p
  exact (congrArg ((system X).stages n).polyhedral
    ((system X).familyRetraction_old n p)).symm

private def intermediateRetraction (n : ℕ) : C((system X).intermediate n, stage X n) :=
  (actualPushoutDesc ((system X).intermediate_isPushout n) (𝟙 (stage X n))
    (TopCat.ofHom (((system X).stages n).polyhedral.comp ((system X).familyRetraction n)))
    (intermediateRetraction_square X n)).hom

private theorem intermediateRetraction_old (n : ℕ) (x : stage X n) :
    intermediateRetraction X n ((system X).oldToIntermediate n x) = x := by
  exact actualPushoutDesc_left ((system X).intermediate_isPushout n) (𝟙 (stage X n))
    (TopCat.ofHom (((system X).stages n).polyhedral.comp ((system X).familyRetraction n)))
    (intermediateRetraction_square X n) x

private theorem intermediateRetraction_family (n : ℕ) (p : ((system X).family n).Realization) :
    intermediateRetraction X n ((system X).familyToIntermediate n p) =
      ((system X).stages n).polyhedral ((system X).familyRetraction n p) := by
  have h := actualPushoutDesc_right (Z := stage X n)
    ((system X).intermediate_isPushout n) (𝟙 (stage X n))
    (TopCat.ofHom (((system X).stages n).polyhedral.comp ((system X).familyRetraction n)))
    (intermediateRetraction_square X n) p
  exact h

private def intermediateFamilyHomotopy (n : ℕ) :
    ContinuousMap.Homotopy ((system X).familyToIntermediate n)
      (((system X).familyToIntermediate n).comp
        (((system X).familyOld n).comp ((system X).familyRetraction n))) :=
  (ContinuousMap.Homotopy.refl ((system X).familyToIntermediate n)).comp
    ((system X).familyDeformation n).toHomotopy

private theorem intermediateHomotopy_square_one (n : ℕ) :
    TopCat.ofHom ((system X).stages n).polyhedral ≫
        TopCat.ofHom ((system X).oldToIntermediate n) =
      TopCat.ofHom ((system X).familyOld n) ≫
        TopCat.ofHom (((system X).familyToIntermediate n).comp
          (((system X).familyOld n).comp ((system X).familyRetraction n))) := by
  apply TopCat.ext
  intro p
  have h := ConcreteCategory.congr_hom ((system X).intermediate_isPushout n).w p
  exact h.trans (congrArg (fun q => (system X).familyToIntermediate n ((system X).familyOld n q))
    ((system X).familyRetraction_old n p).symm)

private theorem intermediateHomotopy_agree (n : ℕ) (t : unitInterval)
    (p : ((system X).stages n).polyhedron.Realization) :
    ContinuousMap.Homotopy.refl ((system X).oldToIntermediate n)
        (t, ((system X).stages n).polyhedral p) =
      intermediateFamilyHomotopy X n (t, (system X).familyOld n p) := by
  have h := ConcreteCategory.congr_hom ((system X).intermediate_isPushout n).w p
  exact h.trans (congrArg ((system X).familyToIntermediate n)
    (((system X).familyDeformation n).eq_fst t (Set.mem_range_self p)).symm)

private def intermediateRawHomotopy (n : ℕ) :=
  actualPushoutHomotopy ((system X).intermediate_isPushout n)
    (ContinuousMap.Homotopy.refl ((system X).oldToIntermediate n))
    (intermediateFamilyHomotopy X n) ((system X).intermediate_isPushout n).w
    (intermediateHomotopy_square_one X n) (intermediateHomotopy_agree X n)

private theorem intermediateRawHomotopy_old (n : ℕ) (t : unitInterval) (x : stage X n) :
    intermediateRawHomotopy X n (t, (system X).oldToIntermediate n x) =
      (system X).oldToIntermediate n x := by
  exact actualPushoutHomotopy_left ((system X).intermediate_isPushout n)
    (ContinuousMap.Homotopy.refl ((system X).oldToIntermediate n))
    (intermediateFamilyHomotopy X n) ((system X).intermediate_isPushout n).w
    (intermediateHomotopy_square_one X n) (intermediateHomotopy_agree X n) t x

private theorem intermediateRawHomotopy_family (n : ℕ) (t : unitInterval)
    (p : ((system X).family n).Realization) :
    intermediateRawHomotopy X n (t, (system X).familyToIntermediate n p) =
      (system X).familyToIntermediate n ((system X).familyDeformation n (t, p)) := by
  have h : intermediateRawHomotopy X n (t, (system X).familyToIntermediate n p) =
      intermediateFamilyHomotopy X n (t, p) :=
    actualPushoutHomotopy_right ((system X).intermediate_isPushout n)
      (ContinuousMap.Homotopy.refl ((system X).oldToIntermediate n))
      (intermediateFamilyHomotopy X n) ((system X).intermediate_isPushout n).w
      (intermediateHomotopy_square_one X n) (intermediateHomotopy_agree X n) t p
  exact h

private def intermediateHomotopy (n : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id ((system X).intermediate n))
      (((system X).oldToIntermediate n).comp (intermediateRetraction X n))
      (Set.range ((system X).oldToIntermediate n)) := by
  let K := intermediateRawHomotopy X n
  refine
    { toFun := K
      continuous_toFun := K.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro a
    rcases Types.eq_or_eq_of_isPushout
      (((system X).intermediate_isPushout n).map (forget TopCat)) a with ha | ha
    · rcases ha with ⟨x, rfl⟩
      exact intermediateRawHomotopy_old X n 0 x
    · rcases ha with ⟨p, rfl⟩
      exact (intermediateRawHomotopy_family X n 0 p).trans
        (congrArg ((system X).familyToIntermediate n)
          (((system X).familyDeformation n).apply_zero p))
  · intro a
    rcases Types.eq_or_eq_of_isPushout
      (((system X).intermediate_isPushout n).map (forget TopCat)) a with ha | ha
    · rcases ha with ⟨x, rfl⟩
      exact (intermediateRawHomotopy_old X n 1 x).trans
        (congrArg ((system X).oldToIntermediate n) (intermediateRetraction_old X n x)).symm
    · rcases ha with ⟨p, rfl⟩
      have h := ConcreteCategory.congr_hom ((system X).intermediate_isPushout n).w
        ((system X).familyRetraction n p)
      exact (intermediateRawHomotopy_family X n 1 p).trans
        ((congrArg ((system X).familyToIntermediate n)
          (((system X).familyDeformation n).apply_one p)).trans
            (h.symm.trans (congrArg ((system X).oldToIntermediate n)
              (intermediateRetraction_family X n p)).symm))
  · intro t a ha
    rcases ha with ⟨x, rfl⟩
    exact intermediateRawHomotopy_old X n t x

private def stageEnd (top : Bool) (n : ℕ) : Set (stage X n) :=
  if top then Set.range ((system X).stages n).polyhedral
  else Set.range ((system X).stages n).original

private def stageRetained (top : Bool) (n : ℕ) : Set (stage X (n + 1)) :=
  Set.range ((system X).transition n) ∪ stageEnd X top (n + 1)

private theorem transition_fixed (top : Bool) (n : ℕ) (t : unitInterval) (x : stage X n) :
    (system X).elementaryHomotopy top n (t, (system X).transition n x) =
      (system X).transition n x := by
  have hi : (system X).transition n x =
      (system X).intermediateToCommon n ((system X).oldToIntermediate n x) :=
    ContinuousMap.congr_fun ((system X).transition_formula n) x
  exact (congrArg (fun a => (system X).elementaryHomotopy top n (t, a)) hi).trans
    (((system X).elementary_fixed_intermediate top n t ((system X).oldToIntermediate n x)).trans
      hi.symm)

private theorem polyhedralDisk_end (n : ℕ)
    (i : Topology.CWComplex.cell (Set.univ : Set X) (n + 1))
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).fst) :
    ((system X).stages (n + 1)).polyhedral ((system X).polyhedralDisks n ⟨i, q⟩) =
      (system X).cylinders n ⟨i, (q, 1)⟩ := by
  let e := (system X).coneDiskComparison n i
  have hd := (system X).polyhedralDisks_value n i q
  have hc := (system X).polyhedral_cone_end n i (e.symm q)
  exact (congrArg ((system X).stages (n + 1)).polyhedral hd).trans
    (hc.trans (congrArg (fun a => (system X).cylinders n ⟨i, (a, 1)⟩)
      (e.apply_symm_apply q)))

private theorem topEnd_fixed (n : ℕ) (t : unitInterval)
    (p : ((system X).stages (n + 1)).polyhedron.Realization) :
    (system X).elementaryHomotopy true n (t, ((system X).stages (n + 1)).polyhedral p) =
      ((system X).stages (n + 1)).polyhedral p := by
  rcases Types.eq_or_eq_of_isPushout
    (((system X).polyhedral_isPushout n).map (forget TopCat)) p with hp | hp
  · rcases hp with ⟨b, rfl⟩
    have h := (system X).polyhedral_cylinder_end n b
    exact (congrArg (fun z => (system X).elementaryHomotopy true n (t, z)) h).trans
      (((system X).elementary_fixed_intermediate true n t
        ((system X).familyToIntermediate n b)).trans h.symm)
  · rcases hp with ⟨⟨i, q⟩, rfl⟩
    have h := polyhedralDisk_end X n i q
    exact (congrArg (fun z => (system X).elementaryHomotopy true n (t, z)) h).trans
      (((system X).elementary_fixed_disk true n t i q).trans h.symm)

private theorem topImage_retained (n : ℕ) :
    Set.range ((system X).elementaryInclude true n) ⊆ stageRetained X true n := by
  intro z hz
  rw [(system X).elementary_image true n] at hz
  rcases hz with ⟨a, rfl⟩ | ⟨⟨i, q⟩, rfl⟩
  · rcases Types.eq_or_eq_of_isPushout
      (((system X).intermediate_isPushout n).map (forget TopCat)) a with ha | ha
    · rcases ha with ⟨x, rfl⟩
      exact Or.inl ⟨x, ContinuousMap.congr_fun ((system X).transition_formula n) x⟩
    · rcases ha with ⟨p, rfl⟩
      exact Or.inr ⟨(system X).familyToNext n p, (system X).polyhedral_cylinder_end n p⟩
  · exact Or.inr ⟨(system X).polyhedralDisks n ⟨i, q⟩, polyhedralDisk_end X n i q⟩

private theorem bottomBoundary_fixed (n : ℕ) (t : unitInterval)
    (b : Topology.CWComplex.CellSpheresAt X (n + 1)) :
    intermediateHomotopy X n (t, (system X).elementaryBoundary false n b) =
      (system X).elementaryBoundary false n b := by
  rcases b with ⟨i, s⟩
  have hb : (system X).elementaryBoundary false n ⟨i, s⟩ =
      (system X).oldToIntermediate n
        (((system X).stages n).original
          (Topology.CWComplex.characteristicSphereToSkeleton (n + 1) i s)) :=
    ((system X).elementaryBoundary_value false n i s).trans
      ((system X).attaching_zero n i s)
  exact (congrArg (fun a => intermediateHomotopy X n (t, a)) hb).trans
    (((intermediateHomotopy X n).eq_fst t
      (Set.mem_range_self (((system X).stages n).original
        (Topology.CWComplex.characteristicSphereToSkeleton (n + 1) i s)))).trans hb.symm)

private def bottomOldMap (n : ℕ) :
    C((system X).intermediate n, (system X).elementarySpace false n) :=
  ((system X).elementaryOld false n).comp
    (((system X).oldToIntermediate n).comp (intermediateRetraction X n))

private theorem bottomSquare_one (n : ℕ) :
    TopCat.ofHom ((system X).elementaryBoundary false n) ≫ TopCat.ofHom (bottomOldMap X n) =
      Topology.CWComplex.sphereSumToDiskSum X (n + 1) ≫
        TopCat.ofHom ((system X).elementaryDisks false n) := by
  apply TopCat.ext
  intro b
  have hR : (system X).oldToIntermediate n
      (intermediateRetraction X n ((system X).elementaryBoundary false n b)) =
        (system X).elementaryBoundary false n b :=
    ((intermediateHomotopy X n).apply_one _).symm.trans (bottomBoundary_fixed X n 1 b)
  exact (congrArg ((system X).elementaryOld false n) hR).trans
    (ConcreteCategory.congr_hom ((system X).elementary_isPushout false n).w b)

private def bottomElementaryRetraction (n : ℕ) :
    C((system X).elementarySpace false n, (system X).elementarySpace false n) :=
  (actualPushoutDesc ((system X).elementary_isPushout false n)
    (TopCat.ofHom (bottomOldMap X n)) (TopCat.ofHom ((system X).elementaryDisks false n))
    (bottomSquare_one X n)).hom

private theorem bottomElementaryRetraction_old (n : ℕ) (a : (system X).intermediate n) :
    bottomElementaryRetraction X n ((system X).elementaryOld false n a) =
      (system X).elementaryOld false n
        ((system X).oldToIntermediate n (intermediateRetraction X n a)) := by
  exact actualPushoutDesc_left ((system X).elementary_isPushout false n)
    (TopCat.ofHom (bottomOldMap X n)) (TopCat.ofHom ((system X).elementaryDisks false n))
    (bottomSquare_one X n) a

private theorem bottomElementaryRetraction_disk (n : ℕ)
    (q : Topology.CWComplex.CellDisksAt X (n + 1)) :
    bottomElementaryRetraction X n ((system X).elementaryDisks false n q) =
      (system X).elementaryDisks false n q := by
  have h := actualPushoutDesc_right (Z := (system X).elementarySpace false n)
    ((system X).elementary_isPushout false n)
    (TopCat.ofHom (bottomOldMap X n)) (TopCat.ofHom ((system X).elementaryDisks false n))
    (bottomSquare_one X n) q
  exact h

private def bottomOldHomotopy (n : ℕ) :
    ContinuousMap.Homotopy ((system X).elementaryOld false n) (bottomOldMap X n) :=
  (ContinuousMap.Homotopy.refl ((system X).elementaryOld false n)).comp
    (intermediateHomotopy X n).toHomotopy

private theorem bottomHomotopy_agree (n : ℕ) (t : unitInterval)
    (b : Topology.CWComplex.CellSpheresAt X (n + 1)) :
    bottomOldHomotopy X n (t, (system X).elementaryBoundary false n b) =
      ContinuousMap.Homotopy.refl ((system X).elementaryDisks false n)
        (t, Topology.CWComplex.sphereSumToDiskSum X (n + 1) b) :=
  (congrArg ((system X).elementaryOld false n) (bottomBoundary_fixed X n t b)).trans
    (ConcreteCategory.congr_hom ((system X).elementary_isPushout false n).w b)

private def bottomRawHomotopy (n : ℕ) :=
  actualPushoutHomotopy ((system X).elementary_isPushout false n)
    (bottomOldHomotopy X n) (ContinuousMap.Homotopy.refl ((system X).elementaryDisks false n))
    ((system X).elementary_isPushout false n).w (bottomSquare_one X n)
    (bottomHomotopy_agree X n)

private theorem bottomRawHomotopy_old (n : ℕ) (t : unitInterval)
    (a : (system X).intermediate n) :
    bottomRawHomotopy X n (t, (system X).elementaryOld false n a) =
      (system X).elementaryOld false n (intermediateHomotopy X n (t, a)) := by
  exact actualPushoutHomotopy_left ((system X).elementary_isPushout false n)
    (bottomOldHomotopy X n) (ContinuousMap.Homotopy.refl ((system X).elementaryDisks false n))
    ((system X).elementary_isPushout false n).w (bottomSquare_one X n)
    (bottomHomotopy_agree X n) t a

private theorem bottomRawHomotopy_disk (n : ℕ) (t : unitInterval)
    (q : Topology.CWComplex.CellDisksAt X (n + 1)) :
    bottomRawHomotopy X n (t, (system X).elementaryDisks false n q) =
      (system X).elementaryDisks false n q := by
  have h : bottomRawHomotopy X n (t, (system X).elementaryDisks false n q) =
      ContinuousMap.Homotopy.refl ((system X).elementaryDisks false n) (t, q) :=
    actualPushoutHomotopy_right ((system X).elementary_isPushout false n)
      (bottomOldHomotopy X n)
      (ContinuousMap.Homotopy.refl ((system X).elementaryDisks false n))
      ((system X).elementary_isPushout false n).w (bottomSquare_one X n)
      (bottomHomotopy_agree X n) t q
  exact h

private def bottomElementaryHomotopy (n : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id ((system X).elementarySpace false n))
      (bottomElementaryRetraction X n) := by
  let K := bottomRawHomotopy X n
  refine
    { toFun := K
      continuous_toFun := K.continuous
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro z
    rcases Types.eq_or_eq_of_isPushout
      (((system X).elementary_isPushout false n).map (forget TopCat)) z with hz | hz
    · rcases hz with ⟨a, rfl⟩
      exact (bottomRawHomotopy_old X n 0 a).trans
        (congrArg ((system X).elementaryOld false n) ((intermediateHomotopy X n).apply_zero a))
    · rcases hz with ⟨q, rfl⟩
      exact bottomRawHomotopy_disk X n 0 q
  · intro z
    exact K.apply_one z

private theorem bottomElementaryHomotopy_old (n : ℕ) (t : unitInterval) (x : stage X n) :
    bottomElementaryHomotopy X n
        (t, (system X).elementaryOld false n ((system X).oldToIntermediate n x)) =
      (system X).elementaryOld false n ((system X).oldToIntermediate n x) :=
  (bottomRawHomotopy_old X n t ((system X).oldToIntermediate n x)).trans
    (congrArg ((system X).elementaryOld false n)
      ((intermediateHomotopy X n).eq_fst t (Set.mem_range_self x)))

private theorem bottomElementaryHomotopy_disk (n : ℕ) (t : unitInterval)
    (q : Topology.CWComplex.CellDisksAt X (n + 1)) :
    bottomElementaryHomotopy X n (t, (system X).elementaryDisks false n q) =
      (system X).elementaryDisks false n q :=
  bottomRawHomotopy_disk X n t q

private theorem bottomEnd_fixed (n : ℕ) (t : unitInterval)
    (x : Topology.CWComplex.skeletonTop X (n + 2)) :
    (system X).elementaryHomotopy false n (t, ((system X).stages (n + 1)).original x) =
      ((system X).stages (n + 1)).original x := by
  rcases Types.eq_or_eq_of_isPushout
    ((Topology.CWComplex.isPushout_skeletonAttachment X (n + 1)).map (forget TopCat)) x
    with hx | hx
  · rcases hx with ⟨a, rfl⟩
    have h := (system X).transition_original n a
    exact (congrArg (fun z => (system X).elementaryHomotopy false n (t, z)) h).trans
      ((transition_fixed X false n t (((system X).stages n).original a)).trans h.symm)
  · rcases hx with ⟨⟨i, q⟩, rfl⟩
    have h := (system X).original_disk_end n i q
    exact (congrArg (fun z => (system X).elementaryHomotopy false n (t, z)) h).trans
      (((system X).elementary_fixed_disk false n t i q).trans h.symm)

private def bottomStageRetraction (n : ℕ) : C(stage X (n + 1), stage X (n + 1)) :=
  ((system X).elementaryInclude false n).comp
    ((bottomElementaryRetraction X n).comp ((system X).elementaryRetraction false n))

private def bottomFirstHomotopy (n : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (stage X (n + 1)))
      (((system X).elementaryInclude false n).comp ((system X).elementaryRetraction false n))
      (stageRetained X false n) := by
  let K := (system X).elementaryHomotopy false n
  refine
    { toFun := K
      continuous_toFun := K.continuous
      map_zero_left := K.apply_zero
      map_one_left := K.apply_one
      prop' := ?_ }
  intro t z hz
  rcases hz with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact transition_fixed X false n t x
  · exact bottomEnd_fixed X n t x

private def bottomSecondHomotopy (n : ℕ) :
    ContinuousMap.Homotopy
      (((system X).elementaryInclude false n).comp ((system X).elementaryRetraction false n))
      (bottomStageRetraction X n) :=
  (ContinuousMap.Homotopy.refl ((system X).elementaryInclude false n)).comp
    ((bottomElementaryHomotopy X n).compContinuousMap ((system X).elementaryRetraction false n))

private theorem bottomSecondHomotopy_old (n : ℕ) (t : unitInterval) (x : stage X n) :
    bottomSecondHomotopy X n (t, (system X).transition n x) = (system X).transition n x := by
  have hi : (system X).transition n x =
      (system X).intermediateToCommon n ((system X).oldToIntermediate n x) :=
    ContinuousMap.congr_fun ((system X).transition_formula n) x
  have hr : (system X).elementaryRetraction false n ((system X).transition n x) =
      (system X).elementaryOld false n ((system X).oldToIntermediate n x) :=
    (congrArg ((system X).elementaryRetraction false n) hi).trans
      ((system X).elementaryRetraction_old false n ((system X).oldToIntermediate n x))
  exact (congrArg (fun e => (system X).elementaryInclude false n
      (bottomElementaryHomotopy X n (t, e))) hr).trans
    ((congrArg ((system X).elementaryInclude false n)
      (bottomElementaryHomotopy_old X n t x)).trans
        (((system X).elementaryInclude_old false n
            ((system X).oldToIntermediate n x)).trans hi.symm))

private theorem bottomSecondHomotopy_disk (n : ℕ) (t : unitInterval)
    (i : Topology.CWComplex.cell (Set.univ : Set X) (n + 1))
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).fst) :
    bottomSecondHomotopy X n (t, (system X).cylinders n ⟨i, (q, 0)⟩) =
      (system X).cylinders n ⟨i, (q, 0)⟩ :=
  (congrArg (fun e => (system X).elementaryInclude false n
    (bottomElementaryHomotopy X n (t, e)))
    ((system X).elementaryRetraction_disk false n i q)).trans
      ((congrArg ((system X).elementaryInclude false n)
        (bottomElementaryHomotopy_disk X n t ⟨i, q⟩)).trans
          ((system X).elementaryInclude_disk false n i q))

private theorem bottomSecondHomotopy_end (n : ℕ) (t : unitInterval)
    (x : Topology.CWComplex.skeletonTop X (n + 2)) :
    bottomSecondHomotopy X n (t, ((system X).stages (n + 1)).original x) =
      ((system X).stages (n + 1)).original x := by
  rcases Types.eq_or_eq_of_isPushout
    ((Topology.CWComplex.isPushout_skeletonAttachment X (n + 1)).map (forget TopCat)) x
    with hx | hx
  · rcases hx with ⟨a, rfl⟩
    have h := (system X).transition_original n a
    exact (congrArg (fun z => bottomSecondHomotopy X n (t, z)) h).trans
      ((bottomSecondHomotopy_old X n t (((system X).stages n).original a)).trans h.symm)
  · rcases hx with ⟨⟨i, q⟩, rfl⟩
    have h := (system X).original_disk_end n i q
    exact (congrArg (fun z => bottomSecondHomotopy X n (t, z)) h).trans
      ((bottomSecondHomotopy_disk X n t i q).trans h.symm)

private def bottomSecondRelativeHomotopy (n : ℕ) :
    ContinuousMap.HomotopyRel
      (((system X).elementaryInclude false n).comp ((system X).elementaryRetraction false n))
      (bottomStageRetraction X n) (stageRetained X false n) := by
  let K := bottomSecondHomotopy X n
  refine
    { toFun := K
      continuous_toFun := K.continuous
      map_zero_left := K.apply_zero
      map_one_left := K.apply_one
      prop' := ?_ }
  intro t z hz
  have hfix : K (t, z) = z := by
    rcases hz with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · exact bottomSecondHomotopy_old X n t x
    · exact bottomSecondHomotopy_end X n t x
  have hfirst : ((system X).elementaryInclude false n)
      ((system X).elementaryRetraction false n z) = z :=
    ((bottomFirstHomotopy X n).apply_one z).symm.trans
      ((bottomFirstHomotopy X n).eq_fst 1 hz)
  exact hfix.trans hfirst.symm

private def bottomStageHomotopy (n : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (stage X (n + 1)))
      (bottomStageRetraction X n) (stageRetained X false n) :=
  (bottomFirstHomotopy X n).trans (bottomSecondRelativeHomotopy X n)

private theorem bottomStageRetraction_image (n : ℕ) (z : stage X (n + 1)) :
    bottomStageRetraction X n z ∈ stageRetained X false n := by
  let e := (system X).elementaryRetraction false n z
  rcases Types.eq_or_eq_of_isPushout
    (((system X).elementary_isPushout false n).map (forget TopCat)) e with he | he
  · rcases he with ⟨a, ha⟩
    have h : bottomStageRetraction X n z =
        (system X).transition n (intermediateRetraction X n a) :=
      (congrArg (fun q => (system X).elementaryInclude false n
        (bottomElementaryRetraction X n q)) ha.symm).trans
          ((congrArg ((system X).elementaryInclude false n)
            (bottomElementaryRetraction_old X n a)).trans
              (((system X).elementaryInclude_old false n
                ((system X).oldToIntermediate n (intermediateRetraction X n a))).trans
                  (ContinuousMap.congr_fun ((system X).transition_formula n)
                    (intermediateRetraction X n a)).symm))
    exact Or.inl ⟨intermediateRetraction X n a, h.symm⟩
  · rcases he with ⟨⟨i, q⟩, hq⟩
    have h : bottomStageRetraction X n z = (system X).cylinders n ⟨i, (q, 0)⟩ :=
      (congrArg (fun a => (system X).elementaryInclude false n
        (bottomElementaryRetraction X n a)) hq.symm).trans
          ((congrArg ((system X).elementaryInclude false n)
            (bottomElementaryRetraction_disk X n ⟨i, q⟩)).trans
              ((system X).elementaryInclude_disk false n i q))
    exact Or.inr ⟨Topology.CWComplex.characteristicDiskToSkeleton (n + 1) i q,
      ((system X).original_disk_end n i q).trans h.symm⟩

private structure StageCollapse (top : Bool) (n : ℕ) where
  retraction : C(stage X (n + 1), stage X (n + 1))
  homotopy : ContinuousMap.HomotopyRel (ContinuousMap.id (stage X (n + 1)))
    retraction (stageRetained X top n)
  image : ∀ z, retraction z ∈ stageRetained X top n

private def actualStageCollapse (top : Bool) (n : ℕ) : StageCollapse X top n := by
  cases top
  · exact
      { retraction := bottomStageRetraction X n
        homotopy := bottomStageHomotopy X n
        image := bottomStageRetraction_image X n }
  · refine
      { retraction := ((system X).elementaryInclude true n).comp
          ((system X).elementaryRetraction true n)
        homotopy := ?_
        image := fun z => topImage_retained X n
          (Set.mem_range_self ((system X).elementaryRetraction true n z)) }
    let K := (system X).elementaryHomotopy true n
    refine
      { toFun := K
        continuous_toFun := K.continuous
        map_zero_left := K.apply_zero
        map_one_left := K.apply_one
        prop' := ?_ }
    intro t z hz
    rcases hz with ⟨x, rfl⟩ | ⟨p, rfl⟩
    · exact transition_fixed X true n t x
    · exact topEnd_fixed X n t p

private abbrev unionData := Topology.CWComplex.commonDimensionUnion.{u, u} X
private abbrev globalSpace : TopCat.{u} := (unionData X).commonCocone.pt
private abbrev commonLeg (n : ℕ) : C(stage X n, globalSpace X) :=
  ((unionData X).commonCocone.ι.app n).hom

private theorem commonLeg_step (n : ℕ) (x : stage X n) :
    commonLeg X (n + 1) ((system X).transition n x) = commonLeg X n x := by
  have h := (unionData X).commonCocone.w (homOfLE (Nat.le_succ n))
  have h' : TopCat.ofHom ((system X).transition n) ≫
      (unionData X).commonCocone.ι.app (n + 1) = (unionData X).commonCocone.ι.app n := by
    simpa only [Functor.ofSequence_map_homOfLE_succ] using! h
  exact ConcreteCategory.congr_hom h' x

private def fixedEnd (top : Bool) : Set (globalSpace X) :=
  if top then Set.range (unionData X).polyhedralEnd else Set.range (unionData X).originalEnd

private theorem fixedEnd_closed (top : Bool) : IsClosed (fixedEnd X top) := by
  cases top
  · exact (unionData X).originalEnd_closed.isClosed_range
  · exact (unionData X).polyhedralEnd_closed.isClosed_range

private theorem fixedEnd_trace (top : Bool) (n : ℕ) :
    (commonLeg X n) ⁻¹' fixedEnd X top = stageEnd X top n := by
  cases top
  · dsimp only [fixedEnd, stageEnd]
    simpa only [Set.image_univ, Set.preimage_univ] using!
      (unionData X).originalEnd_image_stage n (Set.univ : Set X)
  · dsimp only [fixedEnd, stageEnd]
    simpa only [Set.image_univ, Set.preimage_univ] using!
      (unionData X).polyhedralEnd_image_stage n
        (Set.univ : Set (unionData X).polyhedron.Realization)

private def fixedUnionSet (top : Bool) (n : ℕ) : Set (globalSpace X) :=
  fixedEnd X top ∪ Set.range (commonLeg X n)

private abbrev fixedUnion (top : Bool) (n : ℕ) : TopCat.{u} :=
  TopCat.of (fixedUnionSet X top n)

private theorem fixedUnion_closed (top : Bool) (n : ℕ) : IsClosed (fixedUnionSet X top n) :=
  (fixedEnd_closed X top).union ((unionData X).commonStage_closed n).isClosed_range

private theorem fixedUnion_mono_step (top : Bool) (n : ℕ) :
    fixedUnionSet X top n ⊆ fixedUnionSet X top (n + 1) := by
  intro z hz
  rcases hz with he | ⟨x, rfl⟩
  · exact Or.inl he
  · exact Or.inr ⟨(system X).transition n x, commonLeg_step X n x⟩

private def fixedUnionInclusion (top : Bool) (n : ℕ) :
    C(fixedUnion X top n, fixedUnion X top (n + 1)) :=
  ⟨fun x => ⟨x.val, fixedUnion_mono_step X top n x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

private def stageToFixedUnion (top : Bool) (n : ℕ) : C(stage X n, fixedUnion X top n) :=
  ⟨fun x => ⟨commonLeg X n x, Or.inr (Set.mem_range_self x)⟩,
    (commonLeg X n).continuous.subtype_mk _⟩

private def stageRangeHomeomorph (n : ℕ) : stage X n ≃ₜ Set.range (commonLeg X n) := by
  have h : IsEmbedding (commonLeg X n) := ((unionData X).commonStage_closed n).isEmbedding
  exact Topology.IsEmbedding.toHomeomorph (f := commonLeg X n) h

private theorem stageRangeHomeomorph_inverse (n : ℕ) (y : Set.range (commonLeg X n)) :
    commonLeg X n ((stageRangeHomeomorph X n).symm y) = y.val := by
  let e := stageRangeHomeomorph X n
  have he : IsEmbedding (commonLeg X n) := ((unionData X).commonStage_closed n).isEmbedding
  have h₀ : (e (e.symm y)).val = commonLeg X n (e.symm y) :=
    Topology.IsEmbedding.toHomeomorph_apply_coe (f := commonLeg X n) he (e.symm y)
  have h₁ : (e (e.symm y)).val = y.val := congrArg Subtype.val (e.apply_symm_apply y)
  exact h₀.symm.trans h₁

private theorem stageRangeHomeomorph_inverse_image (n : ℕ) (x : stage X n) :
    (stageRangeHomeomorph X n).symm ⟨commonLeg X n x, Set.mem_range_self x⟩ = x := by
  have he : IsEmbedding (commonLeg X n) := ((unionData X).commonStage_closed n).isEmbedding
  exact Topology.IsEmbedding.toHomeomorph_symm_apply (f := commonLeg X n) he x

private def stagePiece (top : Bool) (n : ℕ) : Set (unitInterval × fixedUnion X top (n + 1)) :=
  {p | p.2.val ∈ Set.range (commonLeg X (n + 1))}

private def endPiece (top : Bool) (n : ℕ) : Set (unitInterval × fixedUnion X top (n + 1)) :=
  {p | p.2.val ∈ fixedEnd X top}

private theorem stagePiece_closed (top : Bool) (n : ℕ) : IsClosed (stagePiece X top n) :=
  ((unionData X).commonStage_closed (n + 1)).isClosed_range.preimage
    (continuous_subtype_val.comp continuous_snd)

private theorem endPiece_closed (top : Bool) (n : ℕ) : IsClosed (endPiece X top n) :=
  (fixedEnd_closed X top).preimage (continuous_subtype_val.comp continuous_snd)

private theorem extensionPieces_cover (top : Bool) (n : ℕ) :
    stagePiece X top n ∪ endPiece X top n = Set.univ := by
  ext p
  constructor
  · intro _
    exact Set.mem_univ p
  · intro _
    rcases p.2.property with he | hs
    · exact Or.inr he
    · exact Or.inl hs

private def stagePieceRange (top : Bool) (n : ℕ) :
    C(stagePiece X top n, Set.range (commonLeg X (n + 1))) :=
  ⟨fun p => ⟨p.val.2.val, p.property⟩,
    ((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val).subtype_mk _⟩

private def stagePieceCoordinates (top : Bool) (n : ℕ) :
    C(stagePiece X top n, unitInterval × stage X (n + 1)) :=
  (⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩ :
      C(stagePiece X top n, unitInterval)).prodMk
    (((stageRangeHomeomorph X (n + 1)).symm : C(_, _)).comp (stagePieceRange X top n))

private def stagePieceMap (top : Bool) (n : ℕ) : C(stagePiece X top n, globalSpace X) :=
  (commonLeg X (n + 1)).comp
    (((actualStageCollapse X top n).homotopy.toHomotopy.toContinuousMap).comp
      (stagePieceCoordinates X top n))

private def endPieceMap (top : Bool) (n : ℕ) : C(endPiece X top n, globalSpace X) :=
  ⟨fun p => p.val.2.val, (continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val⟩

private theorem extensionPieces_agree (top : Bool) (n : ℕ)
    (p : unitInterval × fixedUnion X top (n + 1))
    (hs : p ∈ stagePiece X top n) (he : p ∈ endPiece X top n) :
    stagePieceMap X top n ⟨p, hs⟩ = endPieceMap X top n ⟨p, he⟩ := by
  let y : Set.range (commonLeg X (n + 1)) := ⟨p.2.val, hs⟩
  let x := (stageRangeHomeomorph X (n + 1)).symm y
  have hx : commonLeg X (n + 1) x = p.2.val := stageRangeHomeomorph_inverse X (n + 1) y
  have hxE : x ∈ stageEnd X top (n + 1) := by
    have hpEnd : p.2.val ∈ fixedEnd X top := he
    have hxEnd : commonLeg X (n + 1) x ∈ fixedEnd X top :=
      (congrArg (fun z : globalSpace X => z ∈ fixedEnd X top) hx).mpr hpEnd
    have hmem : x ∈ (commonLeg X (n + 1)) ⁻¹' fixedEnd X top := hxEnd
    exact (congrArg (fun s : Set (stage X (n + 1)) => x ∈ s)
      (fixedEnd_trace X top (n + 1))).mp hmem
  exact (congrArg (commonLeg X (n + 1))
    ((actualStageCollapse X top n).homotopy.eq_fst p.1 (Or.inr hxE))).trans hx

private theorem rawExtension_exists (top : Bool) (n : ℕ) :
    ∃ K : C(unitInterval × fixedUnion X top (n + 1), globalSpace X),
      K.restrict (stagePiece X top n) = stagePieceMap X top n ∧
      K.restrict (endPiece X top n) = endPieceMap X top n :=
  TopCat.exists_continuousMap_glue_of_closed_cover
    (X := TopCat.of (unitInterval × fixedUnion X top (n + 1)))
    (Z := globalSpace X) (stagePiece_closed X top n) (endPiece_closed X top n)
    (extensionPieces_cover X top n) (stagePieceMap X top n) (endPieceMap X top n)
    (extensionPieces_agree X top n)

private def rawExtension (top : Bool) (n : ℕ) :
    C(unitInterval × fixedUnion X top (n + 1), globalSpace X) :=
  Classical.choose (rawExtension_exists X top n)

private theorem rawExtension_stage (top : Bool) (n : ℕ) (t : unitInterval)
    (x : stage X (n + 1)) :
    rawExtension X top n (t, stageToFixedUnion X top (n + 1) x) =
      commonLeg X (n + 1) ((actualStageCollapse X top n).homotopy (t, x)) := by
  let p := (t, stageToFixedUnion X top (n + 1) x)
  have hs : p ∈ stagePiece X top n := Set.mem_range_self x
  have h := ContinuousMap.congr_fun
    (Classical.choose_spec (rawExtension_exists X top n)).1 ⟨p, hs⟩
  have hx : (stageRangeHomeomorph X (n + 1)).symm
      (stagePieceRange X top n ⟨p, hs⟩) = x := stageRangeHomeomorph_inverse_image X (n + 1) x
  exact h.trans (congrArg (fun a => commonLeg X (n + 1)
    ((actualStageCollapse X top n).homotopy (t, a))) hx)

private theorem rawExtension_stage_lift (top : Bool) (n : ℕ) (t : unitInterval)
    (b : fixedUnion X top (n + 1)) (x : stage X (n + 1)) (hx : commonLeg X (n + 1) x = b.val) :
    rawExtension X top n (t, b) =
      commonLeg X (n + 1) ((actualStageCollapse X top n).homotopy (t, x)) := by
  have hb : stageToFixedUnion X top (n + 1) x = b := Subtype.ext hx
  exact (congrArg (fun c => rawExtension X top n (t, c)) hb).symm.trans
    (rawExtension_stage X top n t x)

private theorem rawExtension_end (top : Bool) (n : ℕ) (t : unitInterval)
    (b : fixedUnion X top (n + 1)) (hb : b.val ∈ fixedEnd X top) :
    rawExtension X top n (t, b) = b.val :=
  ContinuousMap.congr_fun (Classical.choose_spec (rawExtension_exists X top n)).2
    ⟨(t, b), hb⟩

private theorem rawExtension_zero (top : Bool) (n : ℕ) (b : fixedUnion X top (n + 1)) :
    rawExtension X top n (0, b) = b.val := by
  rcases b.property with hb | ⟨x, hx⟩
  · exact rawExtension_end X top n 0 b hb
  · exact (rawExtension_stage_lift X top n 0 b x hx).trans
      ((congrArg (commonLeg X (n + 1))
          ((actualStageCollapse X top n).homotopy.apply_zero x)).trans hx)

private theorem rawExtension_image (top : Bool) (n : ℕ) (t : unitInterval)
    (b : fixedUnion X top (n + 1)) :
    rawExtension X top n (t, b) ∈ fixedUnionSet X top (n + 1) := by
  rcases b.property with hb | ⟨x, hx⟩
  · exact (rawExtension_end X top n t b hb).symm ▸ Or.inl hb
  · exact Or.inr ⟨(actualStageCollapse X top n).homotopy (t, x),
      (rawExtension_stage_lift X top n t b x hx).symm⟩

private theorem rawExtension_one_image (top : Bool) (n : ℕ)
    (b : fixedUnion X top (n + 1)) :
    rawExtension X top n (1, b) ∈ fixedUnionSet X top n := by
  rcases b.property with hb | ⟨x, hx⟩
  · exact (rawExtension_end X top n 1 b hb).symm ▸ Or.inl hb
  · have h := (rawExtension_stage_lift X top n 1 b x hx).trans
      (congrArg (commonLeg X (n + 1)) ((actualStageCollapse X top n).homotopy.apply_one x))
    rcases (actualStageCollapse X top n).image x with ⟨y, hy⟩ | he
    · exact Or.inr ⟨y, (commonLeg_step X n y).symm.trans
        ((congrArg (commonLeg X (n + 1)) hy).trans h.symm)⟩
    · have he' : commonLeg X (n + 1) ((actualStageCollapse X top n).retraction x) ∈
        fixedEnd X top := by
        exact (congrArg (fun s : Set (stage X (n + 1)) =>
          (actualStageCollapse X top n).retraction x ∈ s)
            (fixedEnd_trace X top (n + 1))).mpr he
      exact h.symm ▸ Or.inl he'

private theorem rawExtension_old_fixed (top : Bool) (n : ℕ) (t : unitInterval)
    (b : fixedUnion X top n) :
    rawExtension X top n (t, fixedUnionInclusion X top n b) = b.val := by
  rcases b.property with hb | ⟨x, hx⟩
  · exact rawExtension_end X top n t (fixedUnionInclusion X top n b) hb
  · have hi : commonLeg X (n + 1) ((system X).transition n x) =
        (fixedUnionInclusion X top n b).val := (commonLeg_step X n x).trans hx
    exact (rawExtension_stage_lift X top n t (fixedUnionInclusion X top n b)
      ((system X).transition n x) hi).trans
        ((congrArg (commonLeg X (n + 1))
          ((actualStageCollapse X top n).homotopy.eq_fst t
            (Or.inl (Set.mem_range_self x)))).trans hi)

private def fixedUnionRetraction (top : Bool) (n : ℕ) :
    C(fixedUnion X top (n + 1), fixedUnion X top n) :=
  ⟨fun b => ⟨rawExtension X top n (1, b), rawExtension_one_image X top n b⟩,
    ((rawExtension X top n).continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩

private def fixedUnionHomotopy (top : Bool) (n : ℕ) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (fixedUnion X top (n + 1)))
      ((fixedUnionInclusion X top n).comp (fixedUnionRetraction X top n))
      (Set.range (fixedUnionInclusion X top n)) := by
  refine
    { toFun := fun p => ⟨rawExtension X top n p, rawExtension_image X top n p.1 p.2⟩
      continuous_toFun := (rawExtension X top n).continuous.subtype_mk _
      map_zero_left := fun b => Subtype.ext (rawExtension_zero X top n b)
      map_one_left := fun _ => Subtype.ext rfl
      prop' := ?_ }
  intro t b hb
  rcases hb with ⟨a, rfl⟩
  exact Subtype.ext (rawExtension_old_fixed X top n t a)

private theorem fixedUnionRetraction_inclusion (top : Bool) (n : ℕ) (b : fixedUnion X top n) :
    fixedUnionRetraction X top n (fixedUnionInclusion X top n b) = b :=
  Subtype.ext (rawExtension_old_fixed X top n 1 b)

private theorem fixedUnionHomotopy_whole_end (top : Bool) (n : ℕ) (t : unitInterval)
    (b : fixedUnion X top (n + 1)) (hb : b.val ∈ fixedEnd X top) :
    fixedUnionHomotopy X top n (t, b) = b :=
  Subtype.ext (rawExtension_end X top n t b hb)

private theorem fixedUnion_zero (top : Bool) : fixedUnionSet X top 0 = fixedEnd X top := by
  have h₀ : Set.range (commonLeg X 0) ⊆ fixedEnd X top := by
    intro z hz
    have h : z ∈ Set.range (unionData X).originalEnd ∩ Set.range (unionData X).polyhedralEnd :=
      (congrArg (fun s : Set (globalSpace X) => z ∈ s)
        (unionData X).global_end_intersection).mpr hz
    cases top
    · exact h.1
    · exact h.2
  exact Set.union_eq_left.mpr h₀

private def endSource : Bool → TopCat.{u}
  | false => X
  | true => TopCat.of (unionData X).polyhedron.Realization

private def endMap : (top : Bool) → C(endSource X top, globalSpace X)
  | false => (unionData X).originalEnd
  | true => (unionData X).polyhedralEnd

private theorem endMap_closed (top : Bool) : IsClosedEmbedding (endMap X top) := by
  cases top
  · exact (unionData X).originalEnd_closed
  · exact (unionData X).polyhedralEnd_closed

private def fixedUnionInitialHomeomorph (top : Bool) : endSource X top ≃ₜ fixedUnion X top 0 := by
  have hrange : Set.range (endMap X top) = fixedEnd X top := by
    cases top <;> rfl
  exact ((endMap_closed X top).isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr (hrange.trans (fixedUnion_zero X top).symm))

private def fixedUnionAmbientInclusion (top : Bool) (n : ℕ) :
    C(fixedUnion X top n, globalSpace X) := ⟨Subtype.val, continuous_subtype_val⟩

private theorem fixedUnionAmbientInclusion_step (top : Bool) (n : ℕ) :
    (fixedUnionAmbientInclusion X top (n + 1)).comp (fixedUnionInclusion X top n) =
      fixedUnionAmbientInclusion X top n := rfl

private theorem fixedUnionInitialHomeomorph_value (top : Bool) (x : endSource X top) :
    (fixedUnionInitialHomeomorph X top x).val = endMap X top x := by
  change (((endMap_closed X top).isEmbedding.toHomeomorph) x).val = endMap X top x
  exact Topology.IsEmbedding.toHomeomorph_apply_coe _ x

private theorem fixedUnion_stage_cover (top : Bool) (z : globalSpace X) :
    ∃ n, ∃ b : fixedUnion X top n, b.val = z := by
  obtain ⟨n, x, hx⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (unionData X).common_isColimit) z
  exact ⟨n, stageToFixedUnion X top n x, hx⟩

end ActualStationaryFixedEndTower
end


noncomputable section

open ContinuousMap Topology
open scoped unitInterval

universe u

namespace StationaryDyadicFiniteSchedulePreparation

private def dyadic (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹

private theorem dyadic_pos (k : ℕ) : 0 < dyadic k :=
  inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) k)

private theorem dyadic_antitone : Antitone dyadic :=
  inv_pow_anti (by norm_num : (1 : ℝ) ≤ 2)

private theorem dyadic_le_one (k : ℕ) : dyadic k ≤ 1 := by
  simpa only [dyadic, pow_zero, inv_one] using dyadic_antitone (Nat.zero_le k)

private def dyadicTime (k : ℕ) : unitInterval :=
  ⟨dyadic k, (dyadic_pos k).le, dyadic_le_one k⟩

private theorem pow_mul_dyadic (k : ℕ) : (2 : ℝ) ^ k * dyadic k = 1 := by
  exact mul_inv_cancel₀ (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0))

private theorem pow_succ_mul_dyadic (k : ℕ) : (2 : ℝ) ^ (k + 1) * dyadic k = 2 := by
  rw [pow_succ]
  calc
    (2 : ℝ) ^ k * 2 * dyadic k = 2 * ((2 : ℝ) ^ k * dyadic k) := by ring
    _ = 2 := by rw [pow_mul_dyadic]; norm_num

private def dyadicClock (k : ℕ) : C(unitInterval, unitInterval) where
  toFun t := Set.projIcc 0 1 zero_le_one ((2 : ℝ) ^ (k + 1) * (t : ℝ) - 1)
  continuous_toFun :=
    (continuous_projIcc : Continuous (Set.projIcc (0 : ℝ) 1 zero_le_one)).comp
    ((continuous_const.mul continuous_subtype_val).sub continuous_const)

private theorem dyadicClock_zero_of_le (k : ℕ) (t : unitInterval)
    (ht : (t : ℝ) ≤ dyadic (k + 1)) : dyadicClock k t = 0 := by
  change Set.projIcc 0 1 zero_le_one ((2 : ℝ) ^ (k + 1) * (t : ℝ) - 1) = 0
  apply (projIcc_eq_zero (x := (2 : ℝ) ^ (k + 1) * (t : ℝ) - 1)).mpr
  have hp : 0 ≤ (2 : ℝ) ^ (k + 1) := (pow_pos (by norm_num) _).le
  have hm : (2 : ℝ) ^ (k + 1) * (t : ℝ) ≤ 1 := by
    calc
      _ ≤ (2 : ℝ) ^ (k + 1) * dyadic (k + 1) := mul_le_mul_of_nonneg_left ht hp
      _ = 1 := pow_mul_dyadic (k + 1)
  linarith

private theorem dyadicClock_one_of_le (k : ℕ) (t : unitInterval)
    (ht : dyadic k ≤ (t : ℝ)) : dyadicClock k t = 1 := by
  change Set.projIcc 0 1 zero_le_one ((2 : ℝ) ^ (k + 1) * (t : ℝ) - 1) = 1
  apply (projIcc_eq_one (x := (2 : ℝ) ^ (k + 1) * (t : ℝ) - 1)).mpr
  have hp : 0 ≤ (2 : ℝ) ^ (k + 1) := (pow_pos (by norm_num) _).le
  have hm : 2 ≤ (2 : ℝ) ^ (k + 1) * (t : ℝ) := by
    calc
      2 = (2 : ℝ) ^ (k + 1) * dyadic k := (pow_succ_mul_dyadic k).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left ht hp
  linarith

private theorem dyadicClock_interval (k : ℕ) (t : unitInterval)
    (ht : (t : ℝ) ∈ Set.Icc (dyadic (k + 1)) (dyadic k)) :
    (dyadicClock k t : ℝ) = (2 : ℝ) ^ (k + 1) * (t : ℝ) - 1 := by
  have hp : 0 ≤ (2 : ℝ) ^ (k + 1) := (pow_pos (by norm_num) _).le
  have hlow : 1 ≤ (2 : ℝ) ^ (k + 1) * (t : ℝ) := by
    calc
      1 = (2 : ℝ) ^ (k + 1) * dyadic (k + 1) := (pow_mul_dyadic (k + 1)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left ht.1 hp
  have hhigh : (2 : ℝ) ^ (k + 1) * (t : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (k + 1) * dyadic k := mul_le_mul_of_nonneg_left ht.2 hp
      _ = 2 := pow_succ_mul_dyadic k
  change (Set.projIcc 0 1 zero_le_one ((2 : ℝ) ^ (k + 1) * (t : ℝ) - 1) : ℝ) = _
  rw [Set.projIcc_of_mem zero_le_one (show (2 : ℝ) ^ (k + 1) * (t : ℝ) - 1 ∈ Set.Icc 0 1 from by
    constructor <;> linarith)]

private theorem dyadicClock_zero (k : ℕ) : dyadicClock k 0 = 0 :=
  dyadicClock_zero_of_le k 0 (dyadic_pos (k + 1)).le

private theorem dyadicClock_one (k : ℕ) : dyadicClock k 1 = 1 :=
  dyadicClock_one_of_le k 1 (dyadic_le_one k)

section Tower

variable (Y : ℕ → Type u) [∀ n, TopologicalSpace (Y n)]
variable (incl : ∀ n, C(Y n, Y (n + 1))) (ret : ∀ n, C(Y (n + 1), Y n))

private def initialInclusion : ∀ n, C(Y 0, Y n)
  | 0 => ContinuousMap.id (Y 0)
  | n + 1 => (incl n).comp (initialInclusion n)

private def initialRetraction : ∀ n, C(Y n, Y 0)
  | 0 => ContinuousMap.id (Y 0)
  | n + 1 => (initialRetraction n).comp (ret n)

variable (ret_incl : ∀ n x, ret n (incl n x) = x)
variable (localH : ∀ n, ContinuousMap.HomotopyRel (ContinuousMap.id (Y (n + 1)))
  ((incl n).comp (ret n)) (Set.range (incl n)))

include ret_incl in
private theorem initialRetraction_inclusion (n : ℕ) (x : Y 0) :
    initialRetraction Y ret n (initialInclusion Y incl n x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change initialRetraction Y ret n (ret n (incl n (initialInclusion Y incl n x))) = x
      rw [ret_incl, ih]

private structure FiniteStageData (n : ℕ) where
  homotopy : ContinuousMap.HomotopyRel (ContinuousMap.id (Y n))
    ((initialInclusion Y incl n).comp (initialRetraction Y ret n))
    (Set.range (initialInclusion Y incl n))
  stationary : ∀ (t : unitInterval) (x : Y n), (t : ℝ) ≤ dyadic n → homotopy (t, x) = x

private def finiteStageStep (n : ℕ) (D : FiniteStageData Y incl ret n) :
    FiniteStageData Y incl ret (n + 1) := by
  let F : unitInterval × Y (n + 1) → Y (n + 1) := fun p =>
    if (p.1 : ℝ) ≤ dyadic n then localH n (dyadicClock n p.1, p.2)
    else incl n (D.homotopy (p.1, ret n p.2))
  have hboundary (p : unitInterval × Y (n + 1)) (hp : (p.1 : ℝ) = dyadic n) :
      localH n (dyadicClock n p.1, p.2) = incl n (D.homotopy (p.1, ret n p.2)) := by
    have hc := dyadicClock_one_of_le n p.1 hp.ge
    have hd := D.stationary p.1 (ret n p.2) hp.le
    have hh := (localH n).apply_one p.2
    calc
      localH n (dyadicClock n p.1, p.2) = incl n (ret n p.2) := by
        simpa only [hc, ContinuousMap.comp_apply] using! hh
      _ = incl n (D.homotopy (p.1, ret n p.2)) := congrArg (incl n) hd.symm
  let K : ContinuousMap.Homotopy (ContinuousMap.id (Y (n + 1)))
      ((initialInclusion Y incl (n + 1)).comp (initialRetraction Y ret (n + 1))) :=
    { toFun := F
      continuous_toFun := by
        have htop : Continuous (fun p : unitInterval × Y (n + 1) =>
            localH n (dyadicClock n p.1, p.2)) :=
          (localH n).toHomotopy.continuous_toFun.comp
            (((dyadicClock n).continuous.comp continuous_fst).prodMk continuous_snd)
        have hbottom : Continuous (fun p : unitInterval × Y (n + 1) =>
            incl n (D.homotopy (p.1, ret n p.2))) :=
          (incl n).continuous.comp (D.homotopy.toHomotopy.continuous_toFun.comp
            (continuous_fst.prodMk ((ret n).continuous.comp continuous_snd)))
        exact continuous_if_le (continuous_subtype_val.comp continuous_fst) continuous_const
          htop.continuousOn hbottom.continuousOn hboundary
      map_zero_left := by
        intro x
        change F (0, x) = x
        dsimp only [F]
        change (if (0 : ℝ) ≤ dyadic n then localH n (dyadicClock n 0, x)
          else incl n (D.homotopy (0, ret n x))) = x
        rw [ite_eq_left (dyadic_pos n).le, dyadicClock_zero]
        exact (localH n).apply_zero x
      map_one_left := by
        intro x
        change F (1, x) = initialInclusion Y incl (n + 1) (initialRetraction Y ret (n + 1) x)
        dsimp only [F]
        split_ifs with ht
        · have hd := D.stationary 1 (ret n x) ht
          have he := D.homotopy.apply_one (ret n x)
          have hy : initialInclusion Y incl n (initialRetraction Y ret n (ret n x)) = ret n x :=
            he.symm.trans hd
          rw [dyadicClock_one]
          have hh := (localH n).apply_one x
          exact hh.trans (congrArg (incl n) hy).symm
        · have he := D.homotopy.apply_one (ret n x)
          exact congrArg (incl n) he }
  refine
    { homotopy :=
        { toHomotopy := K
          prop' := by
            intro t x hx
            rcases hx with ⟨a, rfl⟩
            change F (t, initialInclusion Y incl (n + 1) a) = initialInclusion Y incl (n + 1) a
            dsimp only [F, initialInclusion, ContinuousMap.comp_apply]
            split_ifs with ht
            · exact (localH n).eq_fst (dyadicClock n t)
                (Set.mem_range_self (initialInclusion Y incl n a))
            · rw [ret_incl]
              exact congrArg (incl n)
                (D.homotopy.eq_fst t (Set.mem_range_self a)) }
      stationary := by
        intro t x ht
        change F (t, x) = x
        have hn : dyadic (n + 1) ≤ dyadic n := dyadic_antitone (Nat.le_succ n)
        dsimp only [F]
        rw [ite_eq_left (ht.trans hn), dyadicClock_zero_of_le n t ht]
        exact (localH n).apply_zero x }

private def finiteStageData : ∀ n, FiniteStageData Y incl ret n
  | 0 =>
      { homotopy := (ContinuousMap.HomotopyRel.refl (ContinuousMap.id (Y 0))
          (Set.range (initialInclusion Y incl 0))).cast rfl rfl
        stationary := fun _ _ _ => rfl }
  | n + 1 => finiteStageStep Y incl ret ret_incl localH n (finiteStageData n)

private theorem finiteStageData_succ_apply (n : ℕ) (t : unitInterval) (x : Y (n + 1)) :
    (finiteStageData Y incl ret ret_incl localH (n + 1)).homotopy (t, x) =
      if (t : ℝ) ≤ dyadic n then localH n (dyadicClock n t, x)
      else incl n ((finiteStageData Y incl ret ret_incl localH n).homotopy (t, ret n x)) := rfl

private theorem finiteStageData_stationary (n : ℕ) (t : unitInterval) (x : Y n)
    (ht : (t : ℝ) ≤ dyadic n) :
    (finiteStageData Y incl ret ret_incl localH n).homotopy (t, x) = x :=
  (finiteStageData Y incl ret ret_incl localH n).stationary t x ht

private theorem finiteStageData_succ_after (n : ℕ) (t : unitInterval) (x : Y (n + 1))
    (ht : dyadic n ≤ (t : ℝ)) :
    (finiteStageData Y incl ret ret_incl localH (n + 1)).homotopy (t, x) =
      incl n ((finiteStageData Y incl ret ret_incl localH n).homotopy (t, ret n x)) := by
  rw [finiteStageData_succ_apply]
  split_ifs with h
  · have heq : (t : ℝ) = dyadic n := le_antisymm h ht
    have hc := dyadicClock_one_of_le n t ht
    have hd := finiteStageData_stationary Y incl ret ret_incl localH n t (ret n x) h
    have hh := (localH n).apply_one x
    calc
      localH n (dyadicClock n t, x) = incl n (ret n x) := by
        simpa only [hc, ContinuousMap.comp_apply] using! hh
      _ = incl n ((finiteStageData Y incl ret ret_incl localH n).homotopy (t, ret n x)) :=
        congrArg (incl n) hd.symm
  · rfl

private theorem finiteStageData_boundary (n : ℕ) (x : Y (n + 1)) :
    (finiteStageData Y incl ret ret_incl localH (n + 1)).homotopy (dyadicTime n, x) =
        incl n (ret n x) := by
  have h := finiteStageData_succ_after Y incl ret ret_incl localH n (dyadicTime n) x le_rfl
  have hd := finiteStageData_stationary Y incl ret ret_incl localH n (dyadicTime n) (ret n x) le_rfl
  exact h.trans (congrArg (incl n) hd)

private theorem finiteStageData_same_time_successor (n : ℕ) (t : unitInterval) (x : Y n) :
    (finiteStageData Y incl ret ret_incl localH (n + 1)).homotopy (t, incl n x) =
      incl n ((finiteStageData Y incl ret ret_incl localH n).homotopy (t, x)) := by
  rw [finiteStageData_succ_apply]
  split_ifs with ht
  · have htop := (localH n).eq_fst (dyadicClock n t) (Set.mem_range_self x)
    have hbottom := finiteStageData_stationary Y incl ret ret_incl localH n t x ht
    exact htop.trans (congrArg (incl n) hbottom.symm)
  · rw [ret_incl]

private def towerInclusion : ∀ n k, C(Y n, Y (n + k))
  | n, 0 => ContinuousMap.id (Y n)
  | n, k + 1 => (incl (n + k)).comp (towerInclusion n k)

private def towerRetraction : ∀ n k, C(Y (n + k), Y n)
  | n, 0 => ContinuousMap.id (Y n)
  | n, k + 1 => (towerRetraction n k).comp (ret (n + k))

include ret_incl in
private theorem towerRetraction_inclusion (n k : ℕ) (x : Y n) :
    towerRetraction Y ret n k (towerInclusion Y incl n k x) = x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change towerRetraction Y ret n k
        (ret (n + k) (incl (n + k) (towerInclusion Y incl n k x))) = x
      rw [ret_incl, ih]

private theorem finiteStageData_same_time_all (n k : ℕ) (t : unitInterval) (x : Y n) :
    (finiteStageData Y incl ret ret_incl localH (n + k)).homotopy (t, towerInclusion Y incl n k x) =
      towerInclusion Y incl n k ((finiteStageData Y incl ret ret_incl localH n).homotopy
          (t, x)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (finiteStageData Y incl ret ret_incl localH (n + k + 1)).homotopy
        (t, incl (n + k) (towerInclusion Y incl n k x)) =
        incl (n + k) (towerInclusion Y incl n k
          ((finiteStageData Y incl ret ret_incl localH n).homotopy (t, x)))
      exact (finiteStageData_same_time_successor Y incl ret ret_incl localH
        (n + k) t (towerInclusion Y incl n k x)).trans (congrArg (incl (n + k)) ih)

private theorem finiteStageData_interval (k l : ℕ) (t : unitInterval)
    (ht : (t : ℝ) ∈ Set.Icc (dyadic (k + 1)) (dyadic k))
    (x : Y (k + 1 + l)) :
    (finiteStageData Y incl ret ret_incl localH (k + 1 + l)).homotopy (t, x) =
      towerInclusion Y incl (k + 1) l
        (localH k (dyadicClock k t, towerRetraction Y ret (k + 1) l x)) := by
  induction l with
  | zero =>
      rw [finiteStageData_succ_apply, ite_eq_left ht.2]
      rfl
  | succ l ih =>
      have hle : dyadic (k + 1 + l) ≤ (t : ℝ) :=
        (dyadic_antitone (Nat.le_add_right (k + 1) l)).trans ht.1
      change (finiteStageData Y incl ret ret_incl localH (k + 1 + l + 1)).homotopy (t, x) = _
      have htop := finiteStageData_succ_after Y incl ret ret_incl localH (k + 1 + l) t x hle
      exact htop.trans (congrArg (incl (k + 1 + l)) (ih (ret (k + 1 + l) x)))

end Tower

-- The primitive has only local SDR inputs. The actual X-only theorem must construct those inputs.
end StationaryDyadicFiniteSchedulePreparation
end


noncomputable section
open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex
universe u v
namespace ActualStationaryCommonColimitDescent

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
variable {Y : Type v} [TopologicalSpace Y]

private def commonSequence : ℕ ⥤ TopCat.{u} :=
  Functor.ofSequence (X := fun n => ((commonSuccessorSystem X).stages n).space)
    (fun n => TopCat.ofHom ((commonSuccessorSystem X).transition n))

private def curriedStageFamily
    (K : ∀ n, C(unitInterval × ((commonSuccessorSystem X).stages n).space, Y)) :
    C((Σ n : ℕ, ((commonSuccessorSystem X).stages n).space), C(unitInterval, Y)) :=
  ⟨fun z => ((K z.1).comp ContinuousMap.prodSwap).curry z.2,
    continuous_sigma fun n => ((K n).comp ContinuousMap.prodSwap).curry.continuous⟩

private theorem stageValue_map
    (K : ∀ n, C(unitInterval × ((commonSuccessorSystem X).stages n).space, Y))
    (hK : ∀ n (t : unitInterval) z,
      K (n + 1) (t, (commonSuccessorSystem X).transition n z) = K n (t, z))
    (t : unitInterval) {i j : ℕ} (f : i ⟶ j)
    (z : ((commonSuccessorSystem X).stages i).space) :
    K j (t, (commonSequence X).map f z) = K i (t, z) := by
  have h (i j : ℕ) (hij : i ≤ j) (z : ((commonSuccessorSystem X).stages i).space) :
      K j (t, (commonSequence X).map (homOfLE hij) z) = K i (t, z) := by
    induction j, hij using Nat.le_induction with
    | base =>
        have hid : (commonSequence X).map (homOfLE (le_refl i)) =
            𝟙 ((commonSequence X).obj i) := (commonSequence X).map_id i
        rw [hid]
        rfl
    | succ j hij ih =>
        have he : homOfLE (hij.trans (Nat.le_succ j)) =
            homOfLE hij ≫ homOfLE (Nat.le_succ j) := rfl
        rw [he, Functor.map_comp]
        have hs : ((commonSequence X).map (homOfLE (Nat.le_succ j))).hom =
            (commonSuccessorSystem X).transition j := by
          simp only [commonSequence, Functor.ofSequence_map_homOfLE_succ]
          rfl
        have hp : (commonSequence X).map (homOfLE (Nat.le_succ j))
              ((commonSequence X).map (homOfLE hij) z) =
            (commonSuccessorSystem X).transition j ((commonSequence X).map (homOfLE hij) z) :=
          congrArg (fun g => g ((commonSequence X).map (homOfLE hij) z)) hs
        exact (congrArg (fun y => K (j + 1) (t, y)) hp).trans
          ((hK j t ((commonSequence X).map (homOfLE hij) z)).trans ih)
  simpa only [homOfLE_leOfHom] using! h i j (leOfHom f) z

private theorem curriedStageFamily_factors
    (K : ∀ n, C(unitInterval × ((commonSuccessorSystem X).stages n).space, Y))
    (hK : ∀ n (t : unitInterval) z,
      K (n + 1) (t, (commonSuccessorSystem X).transition n z) = K n (t, z)) :
    Function.FactorsThrough (curriedStageFamily X K)
      (commonDimensionUnion.{u, v} X).commonSigmaQuotient := by
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  let d := commonDimensionUnion.{u, v} X
  let f : i ⟶ max i j := homOfLE (Nat.le_max_left i j)
  let g : j ⟶ max i j := homOfLE (Nat.le_max_right i j)
  have hx : d.commonCocone.ι.app (max i j) ((commonSequence X).map f x) =
      d.commonCocone.ι.app i x := ConcreteCategory.congr_hom (d.commonCocone.w f) x
  have hy : d.commonCocone.ι.app (max i j) ((commonSequence X).map g y) =
      d.commonCocone.ι.app j y := ConcreteCategory.congr_hom (d.commonCocone.w g) y
  have hlegs : d.commonCocone.ι.app i x = d.commonCocone.ι.app j y := by
    exact (d.commonSigmaQuotient_value i x).symm.trans
      (hxy.trans (d.commonSigmaQuotient_value j y))
  have hstage : (commonSequence X).map f x = (commonSequence X).map g y :=
    (d.commonStage_closed (max i j)).injective (hx.trans (hlegs.trans hy.symm))
  apply ContinuousMap.ext
  intro t
  change K i (t, x) = K j (t, y)
  exact (stageValue_map X K hK t f x).symm.trans
    ((congrArg (fun z : ((commonSuccessorSystem X).stages (max i j)).space =>
      K (max i j) (t, z)) hstage).trans (stageValue_map X K hK t g y))

private def curriedUnionFamily
    (K : ∀ n, C(unitInterval × ((commonSuccessorSystem X).stages n).space, Y))
    (hK : ∀ n (t : unitInterval) z,
      K (n + 1) (t, (commonSuccessorSystem X).transition n z) = K n (t, z)) :
    C((commonDimensionUnion.{u, v} X).commonCocone.pt, C(unitInterval, Y)) :=
  ((commonDimensionUnion.{u, v} X).commonSigmaQuotient_isQuotientMap).lift
    (curriedStageFamily X K) (curriedStageFamily_factors X K hK)

private theorem curriedUnionFamily_stage
    (K : ∀ n, C(unitInterval × ((commonSuccessorSystem X).stages n).space, Y))
    (hK : ∀ n (t : unitInterval) z,
      K (n + 1) (t, (commonSuccessorSystem X).transition n z) = K n (t, z))
    (n : ℕ) (t : unitInterval) (z : ((commonSuccessorSystem X).stages n).space) :
    curriedUnionFamily X K hK ((commonDimensionUnion.{u, v} X).commonCocone.ι.app n z) t =
      K n (t, z) := by
  let d := commonDimensionUnion.{u, v} X
  have h := DFunLike.congr_fun (d.commonSigmaQuotient_isQuotientMap.lift_comp
    (curriedStageFamily X K) (curriedStageFamily_factors X K hK)) (⟨n, z⟩ :
      Σ k : ℕ, ((commonSuccessorSystem X).stages k).space)
  have hp := DFunLike.congr_fun h t
  have heq := d.commonSigmaQuotient_value n z
  exact (congrArg (fun y => curriedUnionFamily X K hK y t) heq).symm.trans hp

private def globalUnionFamily
    (K : ∀ n, C(unitInterval × ((commonSuccessorSystem X).stages n).space, Y))
    (hK : ∀ n (t : unitInterval) z,
      K (n + 1) (t, (commonSuccessorSystem X).transition n z) = K n (t, z)) :
    C(unitInterval × (commonDimensionUnion.{u, v} X).commonCocone.pt, Y) :=
  (curriedUnionFamily X K hK).uncurry.comp ContinuousMap.prodSwap

private theorem globalUnionFamily_stage
    (K : ∀ n, C(unitInterval × ((commonSuccessorSystem X).stages n).space, Y))
    (hK : ∀ n (t : unitInterval) z,
      K (n + 1) (t, (commonSuccessorSystem X).transition n z) = K n (t, z))
    (n : ℕ) (t : unitInterval) (z : ((commonSuccessorSystem X).stages n).space) :
    globalUnionFamily X K hK
      (t, (commonDimensionUnion.{u, v} X).commonCocone.ι.app n z) = K n (t, z) :=
  curriedUnionFamily_stage X K hK n t z

end ActualStationaryCommonColimitDescent
end


noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex
open scoped unitInterval

universe u

namespace ActualStationaryGlobalRetractionAssembly

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

private abbrev tower (top : Bool) : ℕ → Type u :=
  fun n => ActualStationaryFixedEndTower.fixedUnion X top n

private abbrev finiteData (top : Bool) (n : ℕ) :=
  StationaryDyadicFiniteSchedulePreparation.finiteStageData
    (tower X top)
    (ActualStationaryFixedEndTower.fixedUnionInclusion X top)
    (ActualStationaryFixedEndTower.fixedUnionRetraction X top)
    (ActualStationaryFixedEndTower.fixedUnionRetraction_inclusion X top)
    (ActualStationaryFixedEndTower.fixedUnionHomotopy X top) n

private abbrev initialInclusion (top : Bool) (n : ℕ) :=
  StationaryDyadicFiniteSchedulePreparation.initialInclusion (tower X top)
    (ActualStationaryFixedEndTower.fixedUnionInclusion X top) n

private abbrev initialRetraction (top : Bool) (n : ℕ) :=
  StationaryDyadicFiniteSchedulePreparation.initialRetraction (tower X top)
    (ActualStationaryFixedEndTower.fixedUnionRetraction X top) n

private theorem initialInclusion_value (top : Bool) (n : ℕ)
    (b : ActualStationaryFixedEndTower.fixedUnion X top 0) :
    (initialInclusion X top n b).val = b.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (ActualStationaryFixedEndTower.fixedUnionInclusion X top n
        (initialInclusion X top n b)).val = b.val
      exact ih

private theorem initialRetraction_step (top : Bool) (n : ℕ)
    (b : ActualStationaryFixedEndTower.fixedUnion X top n) :
    initialRetraction X top (n + 1)
      (ActualStationaryFixedEndTower.fixedUnionInclusion X top n b) =
        initialRetraction X top n b := by
  change initialRetraction X top n
      (ActualStationaryFixedEndTower.fixedUnionRetraction X top n
        (ActualStationaryFixedEndTower.fixedUnionInclusion X top n b)) = _
  rw [ActualStationaryFixedEndTower.fixedUnionRetraction_inclusion]

private theorem stageEntry_step (top : Bool) (n : ℕ)
    (z : ((commonSuccessorSystem X).stages n).space) :
    ActualStationaryFixedEndTower.stageToFixedUnion X top (n + 1)
        ((commonSuccessorSystem X).transition n z) =
      ActualStationaryFixedEndTower.fixedUnionInclusion X top n
        (ActualStationaryFixedEndTower.stageToFixedUnion X top n z) := by
  apply Subtype.ext
  exact ActualStationaryFixedEndTower.commonLeg_step X n z

private def stageRetraction (top : Bool) (n : ℕ) :
    C(((commonSuccessorSystem X).stages n).space, ActualStationaryFixedEndTower.endSource X top) :=
  ((ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top).symm :
    C(ActualStationaryFixedEndTower.fixedUnion X top 0,
      ActualStationaryFixedEndTower.endSource X top)).comp
    ((initialRetraction X top n).comp
      (ActualStationaryFixedEndTower.stageToFixedUnion X top n))

private theorem stageRetraction_step (top : Bool) (n : ℕ)
    (z : ((commonSuccessorSystem X).stages n).space) :
    stageRetraction X top (n + 1) ((commonSuccessorSystem X).transition n z) =
      stageRetraction X top n z := by
  have hs := stageEntry_step X top n z
  have hr := initialRetraction_step X top n
    (ActualStationaryFixedEndTower.stageToFixedUnion X top n z)
  exact (congrArg (fun b => (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top).symm
    (initialRetraction X top (n + 1) b)) hs).trans
      (congrArg (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top).symm hr)

private def constantStageRetractionFamily (top : Bool) (n : ℕ) :
    C(unitInterval × ((commonSuccessorSystem X).stages n).space,
      ActualStationaryFixedEndTower.endSource X top) :=
  (stageRetraction X top n).comp ContinuousMap.snd

private theorem constantStageRetractionFamily_step (top : Bool) (n : ℕ)
    (t : unitInterval) (z : ((commonSuccessorSystem X).stages n).space) :
    constantStageRetractionFamily X top (n + 1) (t, (commonSuccessorSystem X).transition n z) =
      constantStageRetractionFamily X top n (t, z) := stageRetraction_step X top n z

private def stageFamily (top : Bool) (n : ℕ) :
    C(unitInterval × ((commonSuccessorSystem X).stages n).space,
      ActualStationaryFixedEndTower.globalSpace X) :=
  (ActualStationaryFixedEndTower.fixedUnionAmbientInclusion X top n).comp
    ((finiteData X top n).homotopy.toHomotopy.toContinuousMap.comp
      ((ContinuousMap.fst : C(unitInterval × ((commonSuccessorSystem X).stages n).space,
          unitInterval)).prodMk
        ((ActualStationaryFixedEndTower.stageToFixedUnion X top n).comp ContinuousMap.snd)))

private theorem stageFamily_value (top : Bool) (n : ℕ) (t : unitInterval)
    (z : ((commonSuccessorSystem X).stages n).space) :
    stageFamily X top n (t, z) =
      ((finiteData X top n).homotopy
        (t, ActualStationaryFixedEndTower.stageToFixedUnion X top n z)).val := rfl

private theorem stageFamily_step (top : Bool) (n : ℕ) (t : unitInterval)
    (z : ((commonSuccessorSystem X).stages n).space) :
    stageFamily X top (n + 1) (t, (commonSuccessorSystem X).transition n z) =
      stageFamily X top n (t, z) := by
  have he := stageEntry_step X top n z
  have h0 := congrArg (fun b => (finiteData X top (n + 1)).homotopy (t, b)) he
  have h1 := StationaryDyadicFiniteSchedulePreparation.finiteStageData_same_time_successor
    (tower X top)
    (ActualStationaryFixedEndTower.fixedUnionInclusion X top)
    (ActualStationaryFixedEndTower.fixedUnionRetraction X top)
    (ActualStationaryFixedEndTower.fixedUnionRetraction_inclusion X top)
    (ActualStationaryFixedEndTower.fixedUnionHomotopy X top) n t
    (ActualStationaryFixedEndTower.stageToFixedUnion X top n z)
  exact (congrArg Subtype.val h0).trans (congrArg Subtype.val h1)

private theorem stageFamily_zero (top : Bool) (n : ℕ)
    (z : ((commonSuccessorSystem X).stages n).space) :
    stageFamily X top n (0, z) = ActualStationaryFixedEndTower.commonLeg X n z :=
  congrArg Subtype.val ((finiteData X top n).homotopy.apply_zero
    (ActualStationaryFixedEndTower.stageToFixedUnion X top n z))

private theorem initialEnd_value (top : Bool)
    (b : ActualStationaryFixedEndTower.fixedUnion X top 0) :
    b.val = ActualStationaryFixedEndTower.endMap X top
      ((ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top).symm b) := by
  let e := ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top
  have hi := congrArg Subtype.val (e.apply_symm_apply b)
  exact hi.symm.trans
    (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph_value X top (e.symm b))

private theorem stageFamily_one (top : Bool) (n : ℕ)
    (z : ((commonSuccessorSystem X).stages n).space) :
    stageFamily X top n (1, z) =
      ActualStationaryFixedEndTower.endMap X top (stageRetraction X top n z) := by
  let b := ActualStationaryFixedEndTower.stageToFixedUnion X top n z
  have h := congrArg Subtype.val ((finiteData X top n).homotopy.apply_one b)
  have hi := initialInclusion_value X top n (initialRetraction X top n b)
  have he := initialEnd_value X top (initialRetraction X top n b)
  exact h.trans (hi.trans he)

private def globalEndRetraction (top : Bool) :
    C(ActualStationaryFixedEndTower.globalSpace X, ActualStationaryFixedEndTower.endSource X top) :=
  (ActualStationaryCommonColimitDescent.globalUnionFamily
    (Y := ActualStationaryFixedEndTower.endSource X top) X
    (constantStageRetractionFamily X top) (constantStageRetractionFamily_step X top)).comp
    (⟨fun z => (0, z), continuous_const.prodMk continuous_id⟩ :
      C(ActualStationaryFixedEndTower.globalSpace X,
        unitInterval × ActualStationaryFixedEndTower.globalSpace X))

private theorem globalEndRetraction_stage (top : Bool) (n : ℕ)
    (z : ((commonSuccessorSystem X).stages n).space) :
    globalEndRetraction X top (ActualStationaryFixedEndTower.commonLeg X n z) =
      stageRetraction X top n z :=
  ActualStationaryCommonColimitDescent.globalUnionFamily_stage
    (Y := ActualStationaryFixedEndTower.endSource X top) X
    (constantStageRetractionFamily X top) (constantStageRetractionFamily_step X top) n 0 z

private def globalFamily (top : Bool) :
    C(unitInterval × ActualStationaryFixedEndTower.globalSpace X,
      ActualStationaryFixedEndTower.globalSpace X) :=
  ActualStationaryCommonColimitDescent.globalUnionFamily X
    (stageFamily X top) (stageFamily_step X top)

private theorem globalFamily_stage (top : Bool) (n : ℕ) (t : unitInterval)
    (z : ((commonSuccessorSystem X).stages n).space) :
    globalFamily X top (t, ActualStationaryFixedEndTower.commonLeg X n z) =
      stageFamily X top n (t, z) :=
  ActualStationaryCommonColimitDescent.globalUnionFamily_stage X
    (stageFamily X top) (stageFamily_step X top) n t z

private theorem globalStagePresentation (z : ActualStationaryFixedEndTower.globalSpace X) :
    ∃ n, ∃ x : ((commonSuccessorSystem X).stages n).space,
      ActualStationaryFixedEndTower.commonLeg X n x = z :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat)
      (ActualStationaryFixedEndTower.unionData X).common_isColimit) z

private theorem globalFamily_zero (top : Bool) (z : ActualStationaryFixedEndTower.globalSpace X) :
    globalFamily X top (0, z) = z := by
  obtain ⟨n, x, rfl⟩ := globalStagePresentation X z
  exact (globalFamily_stage X top n 0 x).trans (stageFamily_zero X top n x)

private theorem globalFamily_one (top : Bool) (z : ActualStationaryFixedEndTower.globalSpace X) :
    globalFamily X top (1,
        z) = ActualStationaryFixedEndTower.endMap X top (globalEndRetraction X top z) := by
  obtain ⟨n, x, rfl⟩ := globalStagePresentation X z
  exact (globalFamily_stage X top n 1 x).trans
    ((stageFamily_one X top n x).trans
      (congrArg (ActualStationaryFixedEndTower.endMap X top)
          (globalEndRetraction_stage X top n x)).symm)

private theorem stageEntry_of_end (top : Bool)
    (y : ActualStationaryFixedEndTower.endSource X top) (n : ℕ)
    (z : ((commonSuccessorSystem X).stages n).space)
    (hz : ActualStationaryFixedEndTower.commonLeg X n z =
        ActualStationaryFixedEndTower.endMap X top y) :
    ActualStationaryFixedEndTower.stageToFixedUnion X top n z =
      initialInclusion X top n
          (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top y) := by
  apply Subtype.ext
  exact hz.trans
    ((initialInclusion_value X top n
      (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top y)).trans
      (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph_value X top y)).symm

private theorem globalFamily_whole_end (top : Bool) (t : unitInterval)
    (y : ActualStationaryFixedEndTower.endSource X top) :
    globalFamily X top (t, ActualStationaryFixedEndTower.endMap X top y) =
      ActualStationaryFixedEndTower.endMap X top y := by
  obtain ⟨n, z, hz⟩ := globalStagePresentation X (ActualStationaryFixedEndTower.endMap X top y)
  have hb := stageEntry_of_end X top y n z hz
  have h0 := congrArg (fun b => (finiteData X top n).homotopy (t, b)) hb
  have h1 := (finiteData X top n).homotopy.eq_fst t
    (Set.mem_range_self (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top y))
  have hv := (congrArg Subtype.val h0).trans
    ((congrArg Subtype.val h1).trans
      ((initialInclusion_value X top n
        (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top y)).trans
          (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph_value X top y)))
  exact (congrArg (fun a => globalFamily X top (t, a)) hz).symm.trans
    ((globalFamily_stage X top n t z).trans hv)

private theorem globalEndRetraction_end (top : Bool)
    (y : ActualStationaryFixedEndTower.endSource X top) :
    globalEndRetraction X top (ActualStationaryFixedEndTower.endMap X top y) = y := by
  obtain ⟨n, z, hz⟩ := globalStagePresentation X (ActualStationaryFixedEndTower.endMap X top y)
  have hb := stageEntry_of_end X top y n z hz
  have h0 :=
      congrArg (fun b => (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top).symm
    (initialRetraction X top n b)) hb
  have h1 := StationaryDyadicFiniteSchedulePreparation.initialRetraction_inclusion
    (tower X top)
    (ActualStationaryFixedEndTower.fixedUnionInclusion X top)
    (ActualStationaryFixedEndTower.fixedUnionRetraction X top)
    (ActualStationaryFixedEndTower.fixedUnionRetraction_inclusion X top) n
    (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top y)
  have h2 := congrArg (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top).symm h1
  have h3 := (ActualStationaryFixedEndTower.fixedUnionInitialHomeomorph X top).symm_apply_apply y
  exact (congrArg (globalEndRetraction X top) hz).symm.trans
    ((globalEndRetraction_stage X top n z).trans (h0.trans (h2.trans h3)))

private def globalStrongHomotopy (top : Bool) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (ActualStationaryFixedEndTower.globalSpace X))
      ((ActualStationaryFixedEndTower.endMap X top).comp (globalEndRetraction X top))
      (Set.range (ActualStationaryFixedEndTower.endMap X top)) :=
  { toFun := globalFamily X top
    continuous_toFun := (globalFamily X top).continuous
    map_zero_left := globalFamily_zero X top
    map_one_left := globalFamily_one X top
    prop' := by
      intro t z hz
      rcases hz with ⟨y, rfl⟩
      exact globalFamily_whole_end X top t y }

private theorem globalStrongHomotopy_stage (top : Bool) (n : ℕ) (t : unitInterval)
    (z : ((commonSuccessorSystem X).stages n).space) :
    globalStrongHomotopy X top (t, ActualStationaryFixedEndTower.commonLeg X n z) =
      stageFamily X top n (t, z) := globalFamily_stage X top n t z

private theorem globalStrongHomotopy_stationary (top : Bool) (n : ℕ) (t : unitInterval)
    (z : ((commonSuccessorSystem X).stages n).space)
    (ht : (t : ℝ) ≤ StationaryDyadicFiniteSchedulePreparation.dyadic n) :
    globalStrongHomotopy X top (t, ActualStationaryFixedEndTower.commonLeg X n z) =
      ActualStationaryFixedEndTower.commonLeg X n z := by
  have h := (finiteData X top n).stationary t
    (ActualStationaryFixedEndTower.stageToFixedUnion X top n z) ht
  exact (globalStrongHomotopy_stage X top n t z).trans (congrArg Subtype.val h)

private theorem globalStrongHomotopy_shared_zero (top : Bool) (t : unitInterval)
    (j : cell (Set.univ : Set X) 0) :
    globalStrongHomotopy X top
      (t,
          (ActualStationaryFixedEndTower.unionData X).originalEnd
          (map (C := (Set.univ : Set X)) 0 j 0)) =
        (ActualStationaryFixedEndTower.unionData X).originalEnd
            (map (C := (Set.univ : Set X)) 0 j 0) := by
  cases top
  · exact globalFamily_whole_end X false t (map (C := (Set.univ : Set X)) 0 j 0)
  · let d := ActualStationaryFixedEndTower.unionData X
    have he := d.zero_ends_value j
    exact (congrArg (fun a => globalStrongHomotopy X true (t, a)) he).symm.trans
      ((globalFamily_whole_end X true t (d.zeroPolyhedral j)).trans he)

private theorem stageFamily_all_maps (top : Bool) (t : unitInterval) {i j : ℕ}
    (f : i ⟶ j) (z : ((commonSuccessorSystem X).stages i).space) :
    stageFamily X top j (t, (ActualStationaryCommonColimitDescent.commonSequence X).map f z) =
      stageFamily X top i (t, z) :=
  ActualStationaryCommonColimitDescent.stageValue_map X
    (stageFamily X top) (stageFamily_step X top) t f z

private theorem globalStrongHomotopy_interval (top : Bool) (k l : ℕ) (t : unitInterval)
    (ht : (t : ℝ) ∈ Set.Icc
      (StationaryDyadicFiniteSchedulePreparation.dyadic (k + 1))
      (StationaryDyadicFiniteSchedulePreparation.dyadic k))
    (z : ((commonSuccessorSystem X).stages (k + 1 + l)).space) :
    globalStrongHomotopy X top (t, ActualStationaryFixedEndTower.commonLeg X (k + 1 + l) z) =
      (StationaryDyadicFiniteSchedulePreparation.towerInclusion (tower X top)
        (ActualStationaryFixedEndTower.fixedUnionInclusion X top) (k + 1) l
          (ActualStationaryFixedEndTower.fixedUnionHomotopy X top k
            (StationaryDyadicFiniteSchedulePreparation.dyadicClock k t,
              StationaryDyadicFiniteSchedulePreparation.towerRetraction (tower X top)
                (ActualStationaryFixedEndTower.fixedUnionRetraction X top) (k + 1) l
                  (ActualStationaryFixedEndTower.stageToFixedUnion X top (k + 1 + l) z)))).val := by
  have h := StationaryDyadicFiniteSchedulePreparation.finiteStageData_interval
    (tower X top)
    (ActualStationaryFixedEndTower.fixedUnionInclusion X top)
    (ActualStationaryFixedEndTower.fixedUnionRetraction X top)
    (ActualStationaryFixedEndTower.fixedUnionRetraction_inclusion X top)
    (ActualStationaryFixedEndTower.fixedUnionHomotopy X top) k l t ht
    (ActualStationaryFixedEndTower.stageToFixedUnion X top (k + 1 + l) z)
  exact (globalStrongHomotopy_stage X top (k + 1 + l) t z).trans (congrArg Subtype.val h)

private theorem globalEndRetraction_comp_end (top : Bool) :
    (globalEndRetraction X top).comp (ActualStationaryFixedEndTower.endMap X top) =
      ContinuousMap.id (ActualStationaryFixedEndTower.endSource X top) := by
  apply ContinuousMap.ext
  intro y
  exact globalEndRetraction_end X top y

private structure GlobalSDRData (top : Bool) where
  retraction : C(ActualStationaryFixedEndTower.globalSpace X,
      ActualStationaryFixedEndTower.endSource X top)
  retraction_end : ∀ y, retraction (ActualStationaryFixedEndTower.endMap X top y) = y
  homotopy :
      ContinuousMap.HomotopyRel (ContinuousMap.id (ActualStationaryFixedEndTower.globalSpace X))
    ((ActualStationaryFixedEndTower.endMap X top).comp retraction)
    (Set.range (ActualStationaryFixedEndTower.endMap X top))
  stage_stationary : ∀ n (t : unitInterval) (z : ((commonSuccessorSystem X).stages n).space),
    (t : ℝ) ≤ StationaryDyadicFiniteSchedulePreparation.dyadic n →
      homotopy (t, ActualStationaryFixedEndTower.commonLeg X n z) =
          ActualStationaryFixedEndTower.commonLeg X n z

private def actualGlobalSDR (top : Bool) : GlobalSDRData X top :=
  { retraction := globalEndRetraction X top
    retraction_end := globalEndRetraction_end X top
    homotopy := globalStrongHomotopy X top
    stage_stationary := globalStrongHomotopy_stationary X top }

end ActualStationaryGlobalRetractionAssembly
end

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

namespace Topology.CWComplex

/-- The whole fixed end together with the actual common stage, with its literal subspace topology.
`false` selects the original end and `true` selects the constructed weak polyhedral end. -/
public abbrev StationaryDyadicFixedStage (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (top : Bool) (n : ℕ) : TopCat.{u} :=
  TopCat.of (((if top then Set.range (commonDimensionUnion.{u, u} X).polyhedralEnd
      else Set.range (commonDimensionUnion.{u, u} X).originalEnd) ∪
    Set.range ((commonDimensionUnion.{u, u} X).commonCocone.ι.app n)) :
      Set (commonDimensionUnion.{u, u} X).commonCocone.pt)

/-- Both actual end retractions, their whole-end relative homotopies, and the computed local
collapses used in the literal dyadic schedule. All data are outputs of the X-only constructor. -/
public structure StationaryDyadicGlobalRetractionsData (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] where
  /-- A retraction of the common space onto the original end `X` (a left inverse of
  `originalEnd`, by `originalRetraction_end`). -/
  originalRetraction : C((commonDimensionUnion.{u, u} X).commonCocone.pt, X)
  originalRetraction_end : ∀ x,
    originalRetraction ((commonDimensionUnion.{u, u} X).originalEnd x) = x
  /-- A homotopy from the identity of the common space to `originalEnd ∘ originalRetraction`,
  fixing the image of the original end. -/
  originalHomotopy : ContinuousMap.HomotopyRel
    (ContinuousMap.id ((commonDimensionUnion.{u, u} X).commonCocone.pt))
    (((commonDimensionUnion.{u, u} X).originalEnd).comp originalRetraction)
    (Set.range (commonDimensionUnion.{u, u} X).originalEnd)
  /-- A retraction of the common space onto the polyhedral end (a left inverse of
  `polyhedralEnd`, by `polyhedralRetraction_end`). -/
  polyhedralRetraction : C((commonDimensionUnion.{u, u} X).commonCocone.pt,
    (commonDimensionUnion.{u, u} X).polyhedron.Realization)
  polyhedralRetraction_end : ∀ p,
    polyhedralRetraction ((commonDimensionUnion.{u, u} X).polyhedralEnd p) = p
  /-- A homotopy from the identity of the common space to
  `polyhedralEnd ∘ polyhedralRetraction`, fixing the image of the polyhedral end. -/
  polyhedralHomotopy : ContinuousMap.HomotopyRel
    (ContinuousMap.id ((commonDimensionUnion.{u, u} X).commonCocone.pt))
    (((commonDimensionUnion.{u, u} X).polyhedralEnd).comp polyhedralRetraction)
    (Set.range (commonDimensionUnion.{u, u} X).polyhedralEnd)
  /-- The inclusion of fixed stage `n` into fixed stage `n + 1`, for the original end
  (`top = false`) or the polyhedral end (`top = true`); it is the identity on underlying points
  (`localInclusion_value`). -/
  localInclusion : ∀ (top : Bool) (n : ℕ),
    C(StationaryDyadicFixedStage X top n, StationaryDyadicFixedStage X top (n + 1))
  localInclusion_value : ∀ (top : Bool) (n : ℕ) (b : StationaryDyadicFixedStage X top n),
    (localInclusion top n b).val = b.val
  /-- A retraction of fixed stage `n + 1` onto fixed stage `n`, a left inverse of
  `localInclusion` (`localRetraction_inclusion`). -/
  localRetraction : ∀ (top : Bool) (n : ℕ),
    C(StationaryDyadicFixedStage X top (n + 1), StationaryDyadicFixedStage X top n)
  localRetraction_inclusion : ∀ (top : Bool) (n : ℕ)
    (b : StationaryDyadicFixedStage X top n), localRetraction top n (localInclusion top n b) = b
  /-- A homotopy from the identity of fixed stage `n + 1` to
  `localInclusion ∘ localRetraction`, fixing the image of `localInclusion`. -/
  localHomotopy : ∀ (top : Bool) (n : ℕ), ContinuousMap.HomotopyRel
    (ContinuousMap.id (StationaryDyadicFixedStage X top (n + 1)))
    ((localInclusion top n).comp (localRetraction top n)) (Set.range (localInclusion top n))

namespace StationaryDyadicGlobalRetractionsData

variable {X : TopCat.{u}} [T2Space X] [CWComplex (Set.univ : Set X)]

/-- The actual upward tail, computed from the returned local inclusions. -/
public def tailInclusion (d : StationaryDyadicGlobalRetractionsData X) :
    ∀ (top : Bool) (n k : ℕ),
      C(StationaryDyadicFixedStage X top n, StationaryDyadicFixedStage X top (n + k)) := by
  intro top n k
  exact StationaryDyadicFiniteSchedulePreparation.towerInclusion
    (fun j => (StationaryDyadicFixedStage X top j : Type u)) (d.localInclusion top) n k

/-- The actual downward tail, computed from the returned local retractions. -/
public def tailRetraction (d : StationaryDyadicGlobalRetractionsData X) :
    ∀ (top : Bool) (n k : ℕ),
      C(StationaryDyadicFixedStage X top (n + k), StationaryDyadicFixedStage X top n) := by
  intro top n k
  exact StationaryDyadicFiniteSchedulePreparation.towerRetraction
    (fun j => (StationaryDyadicFixedStage X top j : Type u)) (d.localRetraction top) n k

public theorem tailInclusion_zero (d : StationaryDyadicGlobalRetractionsData X)
    (top : Bool) (n : ℕ) : d.tailInclusion top n 0 =
      ContinuousMap.id (StationaryDyadicFixedStage X top n) := by
  change StationaryDyadicFiniteSchedulePreparation.towerInclusion
    (fun j => (StationaryDyadicFixedStage X top j : Type u)) (d.localInclusion top) n 0 = _
  rfl

public theorem tailInclusion_succ (d : StationaryDyadicGlobalRetractionsData X)
    (top : Bool) (n k : ℕ) : d.tailInclusion top n (k + 1) =
      (d.localInclusion top (n + k)).comp (d.tailInclusion top n k) := by
  change StationaryDyadicFiniteSchedulePreparation.towerInclusion
      (fun j => (StationaryDyadicFixedStage X top j : Type u)) (d.localInclusion top) n (k + 1) =
    (d.localInclusion top (n + k)).comp
      (StationaryDyadicFiniteSchedulePreparation.towerInclusion
        (fun j => (StationaryDyadicFixedStage X top j : Type u)) (d.localInclusion top) n k)
  rfl

public theorem tailRetraction_zero (d : StationaryDyadicGlobalRetractionsData X)
    (top : Bool) (n : ℕ) : d.tailRetraction top n 0 =
      ContinuousMap.id (StationaryDyadicFixedStage X top n) := by
  change StationaryDyadicFiniteSchedulePreparation.towerRetraction
    (fun j => (StationaryDyadicFixedStage X top j : Type u)) (d.localRetraction top) n 0 = _
  rfl

public theorem tailRetraction_succ (d : StationaryDyadicGlobalRetractionsData X)
    (top : Bool) (n k : ℕ) : d.tailRetraction top n (k + 1) =
      (d.tailRetraction top n k).comp (d.localRetraction top (n + k)) := by
  change StationaryDyadicFiniteSchedulePreparation.towerRetraction
      (fun j => (StationaryDyadicFixedStage X top j : Type u)) (d.localRetraction top) n (k + 1) =
    (StationaryDyadicFiniteSchedulePreparation.towerRetraction
      (fun j => (StationaryDyadicFixedStage X top j : Type u)) (d.localRetraction top) n k).comp
      (d.localRetraction top (n + k))
  rfl

/-- The same returned global homotopy pulled back along an actual common-stage leg. -/
public def stageFamily (d : StationaryDyadicGlobalRetractionsData X) (top : Bool) (n : ℕ) :
    C(unitInterval × ((commonSuccessorSystem X).stages n).space,
      (commonDimensionUnion.{u, u} X).commonCocone.pt) :=
  (if top then d.polyhedralHomotopy.toHomotopy.toContinuousMap
    else d.originalHomotopy.toHomotopy.toContinuousMap).comp
    ((ContinuousMap.fst :
        C(unitInterval × ((commonSuccessorSystem X).stages n).space, unitInterval)).prodMk
      (((commonDimensionUnion.{u, u} X).commonCocone.ι.app n).hom.comp ContinuousMap.snd))

public theorem stageFamily_apply (d : StationaryDyadicGlobalRetractionsData X)
    (top : Bool) (n : ℕ) (t : unitInterval) (z : ((commonSuccessorSystem X).stages n).space) :
    d.stageFamily top n (t, z) =
      if top then d.polyhedralHomotopy (t, (commonDimensionUnion.{u, u} X).commonCocone.ι.app n z)
      else d.originalHomotopy (t, (commonDimensionUnion.{u, u} X).commonCocone.ι.app n z) := by
  cases top <;> rfl

end StationaryDyadicGlobalRetractionsData

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

/-- Construct both ordinary global strong deformation retractions of the actual common union.
The complete local towers and literal dyadic schedule are constructed from the original X. -/
public def stationaryDyadicGlobalRetractions (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] : StationaryDyadicGlobalRetractionsData X := by
  exact
    { originalRetraction := ActualStationaryGlobalRetractionAssembly.globalEndRetraction X false
      originalRetraction_end := by
        intro x
        exact ActualStationaryGlobalRetractionAssembly.globalEndRetraction_end X false x
      originalHomotopy := ActualStationaryGlobalRetractionAssembly.globalStrongHomotopy X false
      polyhedralRetraction := ActualStationaryGlobalRetractionAssembly.globalEndRetraction X true
      polyhedralRetraction_end := by
        intro p
        exact ActualStationaryGlobalRetractionAssembly.globalEndRetraction_end X true p
      polyhedralHomotopy := ActualStationaryGlobalRetractionAssembly.globalStrongHomotopy X true
      localInclusion := ActualStationaryFixedEndTower.fixedUnionInclusion X
      localInclusion_value := by
        intro top n b
        rfl
      localRetraction := ActualStationaryFixedEndTower.fixedUnionRetraction X
      localRetraction_inclusion := by
        intro top n b
        exact ActualStationaryFixedEndTower.fixedUnionRetraction_inclusion X top n b
      localHomotopy := ActualStationaryFixedEndTower.fixedUnionHomotopy X }

private theorem publicTailInclusion_eq (top : Bool) (n k : ℕ) :
    (stationaryDyadicGlobalRetractions X).tailInclusion top n k =
      StationaryDyadicFiniteSchedulePreparation.towerInclusion
        (ActualStationaryGlobalRetractionAssembly.tower X top)
        (ActualStationaryFixedEndTower.fixedUnionInclusion X top) n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (ActualStationaryFixedEndTower.fixedUnionInclusion X top (n + k)).comp
          ((stationaryDyadicGlobalRetractions X).tailInclusion top n k) =
        (ActualStationaryFixedEndTower.fixedUnionInclusion X top (n + k)).comp
          (StationaryDyadicFiniteSchedulePreparation.towerInclusion
            (ActualStationaryGlobalRetractionAssembly.tower X top)
            (ActualStationaryFixedEndTower.fixedUnionInclusion X top) n k)
      exact congrArg
        (fun f : C(StationaryDyadicFixedStage X top n, StationaryDyadicFixedStage X top (n + k)) =>
          (ActualStationaryFixedEndTower.fixedUnionInclusion X top (n + k)).comp f) ih

private theorem publicTailRetraction_eq (top : Bool) (n k : ℕ) :
    (stationaryDyadicGlobalRetractions X).tailRetraction top n k =
      StationaryDyadicFiniteSchedulePreparation.towerRetraction
        (ActualStationaryGlobalRetractionAssembly.tower X top)
        (ActualStationaryFixedEndTower.fixedUnionRetraction X top) n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((stationaryDyadicGlobalRetractions X).tailRetraction top n k).comp
          (ActualStationaryFixedEndTower.fixedUnionRetraction X top (n + k)) =
        (StationaryDyadicFiniteSchedulePreparation.towerRetraction
          (ActualStationaryGlobalRetractionAssembly.tower X top)
          (ActualStationaryFixedEndTower.fixedUnionRetraction X top) n k).comp
            (ActualStationaryFixedEndTower.fixedUnionRetraction X top (n + k))
      exact congrArg
        (fun f : C(StationaryDyadicFixedStage X top (n + k), StationaryDyadicFixedStage X top n) =>
          f.comp (ActualStationaryFixedEndTower.fixedUnionRetraction X top (n + k))) ih

private theorem publicStageFamily_value (top : Bool) (n : ℕ) (t : unitInterval)
    (z : ((commonSuccessorSystem X).stages n).space) :
    (stationaryDyadicGlobalRetractions X).stageFamily top n (t, z) =
      ActualStationaryGlobalRetractionAssembly.stageFamily X top n (t, z) := by
  rw [StationaryDyadicGlobalRetractionsData.stageFamily_apply]
  cases top
  · change ActualStationaryGlobalRetractionAssembly.globalStrongHomotopy X false
      (t, ActualStationaryFixedEndTower.commonLeg X n z) = _
    exact ActualStationaryGlobalRetractionAssembly.globalStrongHomotopy_stage X false n t z
  · change ActualStationaryGlobalRetractionAssembly.globalStrongHomotopy X true
      (t, ActualStationaryFixedEndTower.commonLeg X n z) = _
    exact ActualStationaryGlobalRetractionAssembly.globalStrongHomotopy_stage X true n t z

public theorem stationaryDyadicGlobalRetractions_originalRetraction_comp_end :
    (stationaryDyadicGlobalRetractions X).originalRetraction.comp
        (commonDimensionUnion.{u, u} X).originalEnd = ContinuousMap.id X := by
  apply ContinuousMap.ext
  intro x
  exact (stationaryDyadicGlobalRetractions X).originalRetraction_end x

public theorem stationaryDyadicGlobalRetractions_polyhedralRetraction_comp_end :
    (stationaryDyadicGlobalRetractions X).polyhedralRetraction.comp
        (commonDimensionUnion.{u, u} X).polyhedralEnd =
      ContinuousMap.id ((commonDimensionUnion.{u, u} X).polyhedron.Realization) := by
  apply ContinuousMap.ext
  intro p
  exact (stationaryDyadicGlobalRetractions X).polyhedralRetraction_end p

/-- Exact same-time compatibility under every actual common-stage arrow. -/
public theorem stationaryDyadicGlobalRetractions_stageFamily_map (top : Bool) (t : unitInterval)
    {i j : ℕ} (f : i ⟶ j) (z : ((commonSuccessorSystem X).stages i).space) :
    (stationaryDyadicGlobalRetractions X).stageFamily top j
        (t, (Functor.ofSequence (X := fun n => ((commonSuccessorSystem X).stages n).space)
          (fun n => TopCat.ofHom ((commonSuccessorSystem X).transition n))).map f z) =
      (stationaryDyadicGlobalRetractions X).stageFamily top i (t, z) := by
  have h := ActualStationaryGlobalRetractionAssembly.stageFamily_all_maps X top t f z
  exact (publicStageFamily_value X top j t _).trans
    (h.trans (publicStageFamily_value X top i t z).symm)

/-- The complete actual stage is fixed before its last dyadic interval. -/
public theorem stationaryDyadicGlobalRetractions_stationary (top : Bool) (n : ℕ)
    (t : unitInterval) (z : ((commonSuccessorSystem X).stages n).space)
    (ht : (t : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹) :
    (stationaryDyadicGlobalRetractions X).stageFamily top n (t, z) =
      (commonDimensionUnion.{u, u} X).commonCocone.ι.app n z := by
  have h := ActualStationaryGlobalRetractionAssembly.globalStrongHomotopy_stationary
    X top n t z ht
  exact (publicStageFamily_value X top n t z).trans
    ((ActualStationaryGlobalRetractionAssembly.globalStrongHomotopy_stage X top n t z).symm.trans h)

/-- Both returned deformations fix every original zero cell at every time. -/
public theorem stationaryDyadicGlobalRetractions_shared_zero (top : Bool) (t : unitInterval)
    (j : cell (Set.univ : Set X) 0) :
    (if top then (stationaryDyadicGlobalRetractions X).polyhedralHomotopy
      (t, (commonDimensionUnion.{u, u} X).originalEnd (map (C := (Set.univ : Set X)) 0 j 0))
    else (stationaryDyadicGlobalRetractions X).originalHomotopy
      (t, (commonDimensionUnion.{u, u} X).originalEnd (map (C := (Set.univ : Set X)) 0 j 0))) =
      (commonDimensionUnion.{u, u} X).originalEnd (map (C := (Set.univ : Set X)) 0 j 0) := by
  cases top
  · exact ActualStationaryGlobalRetractionAssembly.globalStrongHomotopy_shared_zero X false t j
  · exact ActualStationaryGlobalRetractionAssembly.globalStrongHomotopy_shared_zero X true t j

/-- The literal dyadic interval, downward tail, local collapse, and upward tail.
The displayed maps are the fields of this same returned package. -/
public theorem stationaryDyadicGlobalRetractions_interval (top : Bool) (k l : ℕ) (t : unitInterval)
    (ht : (t : ℝ) ∈ Set.Icc (((2 : ℝ) ^ (k + 1))⁻¹) (((2 : ℝ) ^ k)⁻¹))
    (z : ((commonSuccessorSystem X).stages (k + 1 + l)).space) :
    let d := stationaryDyadicGlobalRetractions X
    d.stageFamily top (k + 1 + l) (t, z) =
      (d.tailInclusion top (k + 1) l
        (d.localHomotopy top k
          (Set.projIcc 0 1 zero_le_one ((2 : ℝ) ^ (k + 1) * (t : ℝ) - 1),
            d.tailRetraction top (k + 1) l
              (⟨(commonDimensionUnion.{u, u} X).commonCocone.ι.app (k + 1 + l) z,
                Or.inr (Set.mem_range_self z)⟩ :
                    StationaryDyadicFixedStage X top (k + 1 + l))))).val := by
  let d := stationaryDyadicGlobalRetractions X
  let b : StationaryDyadicFixedStage X top (k + 1 + l) :=
    ⟨(commonDimensionUnion.{u, u} X).commonCocone.ι.app (k + 1 + l) z,
      Or.inr (Set.mem_range_self z)⟩
  let c : unitInterval := Set.projIcc 0 1 zero_le_one ((2 : ℝ) ^ (k + 1) * (t : ℝ) - 1)
  let p : StationaryDyadicFixedStage X top (k + 1) := d.tailRetraction top (k + 1) l b
  let q : StationaryDyadicFixedStage X top (k + 1) :=
    StationaryDyadicFiniteSchedulePreparation.towerRetraction
      (ActualStationaryGlobalRetractionAssembly.tower X top)
      (ActualStationaryFixedEndTower.fixedUnionRetraction X top) (k + 1) l b
  have hp : p = q := ContinuousMap.congr_fun (publicTailRetraction_eq X top (k + 1) l) b
  have hlocal : d.localHomotopy top k (c, p) =
      ActualStationaryFixedEndTower.fixedUnionHomotopy X top k
        (StationaryDyadicFiniteSchedulePreparation.dyadicClock k t, q) := by
    exact congrArg (fun x => ActualStationaryFixedEndTower.fixedUnionHomotopy X top k (c, x)) hp
  have htail : d.tailInclusion top (k + 1) l (d.localHomotopy top k (c, p)) =
      StationaryDyadicFiniteSchedulePreparation.towerInclusion
        (ActualStationaryGlobalRetractionAssembly.tower X top)
        (ActualStationaryFixedEndTower.fixedUnionInclusion X top) (k + 1) l
          (ActualStationaryFixedEndTower.fixedUnionHomotopy X top k
            (StationaryDyadicFiniteSchedulePreparation.dyadicClock k t, q)) :=
    (ContinuousMap.congr_fun (publicTailInclusion_eq X top (k + 1) l) _).trans
      (congrArg (StationaryDyadicFiniteSchedulePreparation.towerInclusion
        (ActualStationaryGlobalRetractionAssembly.tower X top)
        (ActualStationaryFixedEndTower.fixedUnionInclusion X top) (k + 1) l) hlocal)
  have h := ActualStationaryGlobalRetractionAssembly.globalStrongHomotopy_interval X top k l t ht z
  exact ((publicStageFamily_value X top (k + 1 + l) t z).trans
      (ActualStationaryGlobalRetractionAssembly.globalStrongHomotopy_stage
        X top (k + 1 + l) t z).symm).trans
    (h.trans (congrArg Subtype.val htail).symm)

end Topology.CWComplex
end
