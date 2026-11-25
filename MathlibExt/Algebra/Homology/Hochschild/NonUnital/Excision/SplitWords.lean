/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.Kernels
public import MathlibExt.Algebra.Algebra.NonUnitalIdeal.KSplit
public import MathlibExt.Algebra.NonUnitalSubalgebra.Quotient
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Fintype.BigOperators

/-!
# Split-word tensor coordinates

A color selects an ideal or quotient module
at each tensor position. The ideal inclusion
and a ground-linear quotient section define
ambient word maps; ideal projections and
the quotient map recover the coordinates.
Distinct colors are orthogonal and their
finite sum reconstructs the word. The
coefficient module has an independent universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

/-- One original ideal or quotient entry, in the original algebra universe. -/
def splitWordEntry (colour : Bool) : ModuleCat.{v} k :=
  if colour then ModuleCat.of k I.Quotient else ModuleCat.of k I.Algebra

/-- The original inclusion or original section for one entry. -/
def splitWordEntryMap (splitting : I.KSplit) (colour : Bool) :
    splitWordEntry k A I colour →ₗ[k] A := by
  cases colour with
  | false => exact (I.subtypeHom : I.Algebra →ₗ[k] A)
  | true => exact splitting.sectionMap

/-- The original ideal projection or the original quotient map. -/
def splitWordEntryProjection (splitting : I.KSplit) (colour : Bool) :
    A →ₗ[k] splitWordEntry k A I colour := by
  cases colour with
  | false => exact splitting.projection
  | true => exact NonUnitalSubalgebra.Quotient.mkL I

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Each original entry is recovered by its coordinate. -/
theorem splitWordEntryProjection_leftInverse (splitting : I.KSplit) (colour : Bool)
    (a : splitWordEntry k A I colour) :
    splitWordEntryProjection k A I splitting colour
        (splitWordEntryMap k A I splitting colour a) = a := by
  cases colour with
  | false => exact splitting.projection_subtype a
  | true => exact splitting.quotient_section a

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The two distinct original entry coordinates annihilate one another. -/
theorem splitWordEntryProjection_map_zero (splitting : I.KSplit)
    (source target : Bool) (h : source ≠ target)
    (a : splitWordEntry k A I source) :
    splitWordEntryProjection k A I splitting target
        (splitWordEntryMap k A I splitting source a) = 0 := by
  cases source <;> cases target
  · exact False.elim (h rfl)
  · change NonUnitalSubalgebra.Quotient.mkL I a.val = 0
    exact (Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr a.property
  · exact splitting.projection_section a
  · exact False.elim (h rfl)

variable {N : ℕ}

/-- The canonical module in every original coloured position. -/
def splitWordPosition (colour : Fin N → Bool) (i : Fin N) : ModuleCat.{v} k :=
  splitWordEntry k A I (colour i)

/-- The original entry map at the original coloured position. -/
def splitWordPositionMap (splitting : I.KSplit) (colour : Fin N → Bool) (i : Fin N) :
    splitWordPosition k A I colour i →ₗ[k] A :=
  splitWordEntryMap k A I splitting (colour i)

/-- The original coordinate map at the same original position. -/
def splitWordPositionProjection (splitting : I.KSplit) (colour : Fin N → Bool)
    (i : Fin N) : A →ₗ[k] splitWordPosition k A I colour i :=
  splitWordEntryProjection k A I splitting (colour i)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The original typed entry is recovered in the same position. -/
theorem splitWordPositionProjection_leftInverse (splitting : I.KSplit)
    (colour : Fin N → Bool) (i : Fin N) (a : splitWordPosition k A I colour i) :
    splitWordPositionProjection k A I splitting colour i
        (splitWordPositionMap k A I splitting colour i a) = a :=
  splitWordEntryProjection_leftInverse k A I splitting (colour i) a

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- A distinct colour at one original position gives the original zero coordinate. -/
theorem splitWordPositionProjection_map_zero (splitting : I.KSplit)
    (source target : Fin N → Bool) (i : Fin N) (h : source i ≠ target i)
    (a : splitWordPosition k A I source i) :
    splitWordPositionProjection k A I splitting target i
        (splitWordPositionMap k A I splitting source i a) = 0 :=
  splitWordEntryProjection_map_zero k A I splitting (source i) (target i) h a

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Every original ideal entry has zero original quotient coordinate. -/
theorem splitWordPositionProjection_ideal_zero (splitting : I.KSplit)
    (colour : Fin N → Bool) (i : Fin N) (hi : colour i = true)
    (a : A) (ha : a ∈ I.toSubmodule) :
    splitWordPositionProjection k A I splitting colour i a = 0 := by
  change splitWordEntryProjection k A I splitting (colour i) a = 0
  rw [hi]
  change NonUnitalSubalgebra.Quotient.mkL I a = 0
  exact (Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr ha

/-- The original variable-module tensor of all original coloured positions. -/
abbrev splitWordTensor (colour : Fin N → Bool) : Type (max u v) :=
  PiTensorProduct k (fun i : Fin N => splitWordPosition k A I colour i)

/-- The original coloured word map into the original ambient tensor. -/
def splitWordToAmbient (splitting : I.KSplit) (colour : Fin N → Bool) :
    splitWordTensor k A I colour →ₗ[k] TensorPower k N A :=
  PiTensorProduct.map (splitWordPositionMap k A I splitting colour)

/-- The original coordinate map out of the original ambient tensor. -/
def splitAmbientToWord (splitting : I.KSplit) (colour : Fin N → Bool) :
    TensorPower k N A →ₗ[k] splitWordTensor k A I colour :=
  PiTensorProduct.map (splitWordPositionProjection k A I splitting colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- All original entry maps retain their original tensor positions. -/
theorem splitWordToAmbient_tprod (splitting : I.KSplit) (colour : Fin N → Bool)
    (a : ∀ i : Fin N, splitWordPosition k A I colour i) :
    splitWordToAmbient k A I splitting colour (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k
        (fun i => splitWordPositionMap k A I splitting colour i (a i)) :=
  PiTensorProduct.map_tprod _ _

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- All original entry coordinates read their original tensor positions. -/
theorem splitAmbientToWord_tprod (splitting : I.KSplit) (colour : Fin N → Bool)
    (a : Fin N → A) :
    splitAmbientToWord k A I splitting colour (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k
        (fun i => splitWordPositionProjection k A I splitting colour i (a i)) :=
  PiTensorProduct.map_tprod _ _

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The original entry retractions earn the coloured tensor retraction. -/
theorem splitAmbientToWord_comp_splitWordToAmbient (splitting : I.KSplit)
    (colour : Fin N → Bool) :
    (splitAmbientToWord k A I splitting colour).comp
        (splitWordToAmbient k A I splitting colour) = LinearMap.id := by
  have hi (i : Fin N) :
      (splitWordPositionProjection k A I splitting colour i).comp
          (splitWordPositionMap k A I splitting colour i) = LinearMap.id := by
    apply LinearMap.ext
    intro a
    exact splitWordPositionProjection_leftInverse k A I splitting colour i a
  rw [splitAmbientToWord, splitWordToAmbient, ← PiTensorProduct.map_comp]
  simp_rw [hi]
  exact PiTensorProduct.map_id

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Distinct complete colour coordinates annihilate the other coloured tensor map. -/
theorem splitAmbientToWord_comp_splitWordToAmbient_zero (splitting : I.KSplit)
    (source target : Fin N → Bool) (h : source ≠ target) :
    (splitAmbientToWord k A I splitting target).comp
        (splitWordToAmbient k A I splitting source) = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin N, source i ≠ target i := by
    by_contra hn
    apply h
    funext i
    by_contra hi
    exact hn ⟨i, hi⟩
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  change splitAmbientToWord k A I splitting target
      (splitWordToAmbient k A I splitting source (PiTensorProduct.tprod k a)) = 0
  rw [splitWordToAmbient_tprod, splitAmbientToWord_tprod]
  exact (PiTensorProduct.tprod k).map_coord_zero i
    (splitWordPositionProjection_map_zero k A I splitting source target i hi (a i))

private def splitWordEntryEnd (splitting : I.KSplit) (colour : Bool) : A →ₗ[k] A :=
  (splitWordEntryMap k A I splitting colour).comp
    (splitWordEntryProjection k A I splitting colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem splitWordEntryEnd_sum (splitting : I.KSplit) :
    (∑ colour : Bool, splitWordEntryEnd k A I splitting colour) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  rw [Fintype.sum_bool, LinearMap.add_apply]
  change splitting.sectionMap (NonUnitalSubalgebra.Quotient.mkL I a) +
    (splitting.projection a : A) = a
  rw [add_comm]
  exact splitting.reconstruct a

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Finite multilinearity reconstructs the original ambient tensor from all original colours. -/
theorem splitWordToAmbient_sum_comp_splitAmbientToWord (splitting : I.KSplit) (N : ℕ) :
    (∑ colour : Fin N → Bool,
      (splitWordToAmbient k A I splitting colour).comp
        (splitAmbientToWord k A I splitting colour)) = LinearMap.id := by
  classical
  have hexpand :
      PiTensorProduct.map
          (fun _ : Fin N => ∑ b : Bool, splitWordEntryEnd k A I splitting b) =
        ∑ colour : Fin N → Bool,
          PiTensorProduct.map (fun i => splitWordEntryEnd k A I splitting (colour i)) :=
    (PiTensorProduct.mapMultilinear k (fun _ : Fin N => A) (fun _ : Fin N => A)).map_sum
      (fun (_ : Fin N) (b : Bool) => splitWordEntryEnd k A I splitting b)
  rw [splitWordEntryEnd_sum, PiTensorProduct.map_id] at hexpand
  calc
    (∑ colour : Fin N → Bool,
        (splitWordToAmbient k A I splitting colour).comp
          (splitAmbientToWord k A I splitting colour)) =
        ∑ colour : Fin N → Bool,
          PiTensorProduct.map (fun i => splitWordEntryEnd k A I splitting (colour i)) := by
      apply Finset.sum_congr rfl
      intro colour _
      rw [splitWordToAmbient, splitAmbientToWord, ← PiTensorProduct.map_comp]
      rfl
    _ = LinearMap.id := hexpand.symm

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Every original ambient tensor equals its finite sum of original colour coordinates. -/
theorem splitWord_reconstruct (splitting : I.KSplit) (x : TensorPower k N A) :
    (∑ colour : Fin N → Bool,
      splitWordToAmbient k A I splitting colour
        (splitAmbientToWord k A I splitting colour x)) = x := by
  have h := congrArg (fun f : TensorPower k N A →ₗ[k] TensorPower k N A => f x)
    (splitWordToAmbient_sum_comp_splitAmbientToWord k A I splitting N)
  simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.id_apply] using h

/-- The finite family of all original coloured tensor coordinates. -/
abbrev splitWordCoordinates (N : ℕ) : Type (max u v) :=
  ∀ colour : Fin N → Bool, splitWordTensor k A I colour

/-- The native finite-product map collecting every original coordinate. -/
def ambientToSplitWordCoordinates (splitting : I.KSplit) (N : ℕ) :
    TensorPower k N A →ₗ[k] splitWordCoordinates k A I N :=
  LinearMap.pi (fun colour => splitAmbientToWord k A I splitting colour)

/-- The native finite sum of the original coloured word maps. -/
def splitWordCoordinatesToAmbient (splitting : I.KSplit) (N : ℕ) :
    splitWordCoordinates k A I N →ₗ[k] TensorPower k N A :=
  ∑ colour : Fin N → Bool,
    (splitWordToAmbient k A I splitting colour).comp (LinearMap.proj colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Actual all-colour reconstruction earns one inverse identity on the original ambient tensor. -/
theorem splitWordCoordinatesToAmbient_comp_ambientToSplitWordCoordinates
    (splitting : I.KSplit) (N : ℕ) :
    (splitWordCoordinatesToAmbient k A I splitting N).comp
        (ambientToSplitWordCoordinates k A I splitting N) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (∑ colour : Fin N → Bool,
      (splitWordToAmbient k A I splitting colour).comp (LinearMap.proj colour))
        (ambientToSplitWordCoordinates k A I splitting N x) = x
  simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    ambientToSplitWordCoordinates, LinearMap.pi_apply] using
      (splitWord_reconstruct k A I splitting x)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Actual colour orthogonality earns the other inverse identity on the complete coordinate family. -/
theorem ambientToSplitWordCoordinates_comp_splitWordCoordinatesToAmbient
    (splitting : I.KSplit) (N : ℕ) :
    (ambientToSplitWordCoordinates k A I splitting N).comp
        (splitWordCoordinatesToAmbient k A I splitting N) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  funext target
  change splitAmbientToWord k A I splitting target
      ((∑ source : Fin N → Bool,
        (splitWordToAmbient k A I splitting source).comp (LinearMap.proj source)) x) = x target
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [map_sum]
  have hterm (source : Fin N → Bool) :
      splitAmbientToWord k A I splitting target
          (splitWordToAmbient k A I splitting source (x source)) =
        if source = target then x target else 0 := by
    by_cases h : source = target
    · subst source
      rw [ite_eq_left rfl]
      exact congrArg (fun f => f (x target))
        (splitAmbientToWord_comp_splitWordToAmbient k A I splitting target)
    · rw [ite_eq_right h]
      exact congrArg (fun f => f (x source))
        (splitAmbientToWord_comp_splitWordToAmbient_zero k A I splitting source target h)
  simp_rw [hterm]
  simp

/-- The source linear splitting earns the finite equivalence of all original tensor coordinates. -/
def splitWordCoordinatesEquiv (splitting : I.KSplit) (N : ℕ) :
    splitWordCoordinates k A I N ≃ₗ[k] TensorPower k N A :=
  { splitWordCoordinatesToAmbient k A I splitting N with
    invFun := ambientToSplitWordCoordinates k A I splitting N
    left_inv := fun x => congrArg (fun f => f x)
      (ambientToSplitWordCoordinates_comp_splitWordCoordinatesToAmbient k A I splitting N)
    right_inv := fun x => congrArg (fun f => f x)
      (splitWordCoordinatesToAmbient_comp_ambientToSplitWordCoordinates k A I splitting N) }

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The equivalence uses precisely the sum of the original section/inclusion tensor maps. -/
theorem splitWordCoordinatesEquiv_apply (splitting : I.KSplit) (N : ℕ)
    (x : splitWordCoordinates k A I N) :
    splitWordCoordinatesEquiv k A I splitting N x =
      ∑ colour : Fin N → Bool, splitWordToAmbient k A I splitting colour (x colour) := by
  change (∑ colour : Fin N → Bool,
    (splitWordToAmbient k A I splitting colour).comp (LinearMap.proj colour)) x = _
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The inverse uses precisely the original projection/quotient tensor maps. -/
theorem splitWordCoordinatesEquiv_symm_apply (splitting : I.KSplit) (N : ℕ)
    (x : TensorPower k N A) (colour : Fin N → Bool) :
    (splitWordCoordinatesEquiv k A I splitting N).symm x colour =
      splitAmbientToWord k A I splitting colour x := rfl

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- The arbitrary coefficient is retained by identity in every original coloured word map. -/
def coefficientSplitWordToAmbient (splitting : I.KSplit) (colour : Fin N → Bool) :
    V ⊗[k] splitWordTensor k A I colour →ₗ[k] V ⊗[k] TensorPower k N A :=
  TensorProduct.map (LinearMap.id : V →ₗ[k] V)
    (splitWordToAmbient k A I splitting colour)

/-- The arbitrary coefficient is retained by identity in every original coordinate. -/
def coefficientSplitAmbientToWord (splitting : I.KSplit) (colour : Fin N → Bool) :
    V ⊗[k] TensorPower k N A →ₗ[k] V ⊗[k] splitWordTensor k A I colour :=
  TensorProduct.map (LinearMap.id : V →ₗ[k] V)
    (splitAmbientToWord k A I splitting colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Original coefficient and position values retain their original tensor positions. -/
theorem coefficientSplitWordToAmbient_tprod (splitting : I.KSplit)
    (colour : Fin N → Bool) (v : V)
    (a : ∀ i : Fin N, splitWordPosition k A I colour i) :
    coefficientSplitWordToAmbient k A I V splitting colour
        (v ⊗ₜ[k] PiTensorProduct.tprod k a) =
      v ⊗ₜ[k] PiTensorProduct.tprod k
        (fun i => splitWordPositionMap k A I splitting colour i (a i)) := by
  rw [coefficientSplitWordToAmbient, TensorProduct.map_tmul, LinearMap.id_apply,
    splitWordToAmbient_tprod]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The coefficient and every original coordinate are read by the original maps. -/
theorem coefficientSplitAmbientToWord_tprod (splitting : I.KSplit)
    (colour : Fin N → Bool) (v : V) (a : Fin N → A) :
    coefficientSplitAmbientToWord k A I V splitting colour
        (v ⊗ₜ[k] PiTensorProduct.tprod k a) =
      v ⊗ₜ[k] PiTensorProduct.tprod k
        (fun i => splitWordPositionProjection k A I splitting colour i (a i)) := by
  rw [coefficientSplitAmbientToWord, TensorProduct.map_tmul, LinearMap.id_apply,
    splitAmbientToWord_tprod]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Original position retractions earn the same retraction with arbitrary coefficient. -/
theorem coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient
    (splitting : I.KSplit) (colour : Fin N → Bool) :
    (coefficientSplitAmbientToWord k A I V splitting colour).comp
        (coefficientSplitWordToAmbient k A I V splitting colour) = LinearMap.id := by
  rw [coefficientSplitAmbientToWord, coefficientSplitWordToAmbient,
    ← TensorProduct.map_comp, LinearMap.id_comp, splitAmbientToWord_comp_splitWordToAmbient]
  exact TensorProduct.map_id

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Distinct complete colour coordinates annihilate the other arbitrary-coefficient word map. -/
theorem coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient_zero
    (splitting : I.KSplit) (source target : Fin N → Bool) (h : source ≠ target) :
    (coefficientSplitAmbientToWord k A I V splitting target).comp
        (coefficientSplitWordToAmbient k A I V splitting source) = 0 := by
  rw [coefficientSplitAmbientToWord, coefficientSplitWordToAmbient,
    ← TensorProduct.map_comp, LinearMap.id_comp,
    splitAmbientToWord_comp_splitWordToAmbient_zero k A I splitting source target h]
  exact TensorProduct.map_zero_right _

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Native tensor functoriality retains the full original all-colour reconstruction under arbitrary V. -/
theorem coefficientSplitWordToAmbient_sum_comp_coefficientSplitAmbientToWord
    (splitting : I.KSplit) (N : ℕ) :
    (∑ colour : Fin N → Bool,
      (coefficientSplitWordToAmbient k A I V splitting colour).comp
        (coefficientSplitAmbientToWord k A I V splitting colour)) = LinearMap.id := by
  classical
  have hsum :
      TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (∑ colour : Fin N → Bool,
            (splitWordToAmbient k A I splitting colour).comp
              (splitAmbientToWord k A I splitting colour)) =
        ∑ colour : Fin N → Bool,
          TensorProduct.map (LinearMap.id : V →ₗ[k] V)
            ((splitWordToAmbient k A I splitting colour).comp
              (splitAmbientToWord k A I splitting colour)) :=
    map_sum (LinearMap.lTensorHom V) _ _
  calc
    (∑ colour : Fin N → Bool,
        (coefficientSplitWordToAmbient k A I V splitting colour).comp
          (coefficientSplitAmbientToWord k A I V splitting colour)) =
        ∑ colour : Fin N → Bool,
          TensorProduct.map (LinearMap.id : V →ₗ[k] V)
            ((splitWordToAmbient k A I splitting colour).comp
              (splitAmbientToWord k A I splitting colour)) := by
      apply Finset.sum_congr rfl
      intro colour _
      rw [coefficientSplitWordToAmbient, coefficientSplitAmbientToWord,
        ← TensorProduct.map_comp, LinearMap.id_comp]
    _ = TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (∑ colour : Fin N → Bool,
            (splitWordToAmbient k A I splitting colour).comp
              (splitAmbientToWord k A I splitting colour)) := hsum.symm
    _ = LinearMap.id := by
      rw [splitWordToAmbient_sum_comp_splitAmbientToWord]
      exact TensorProduct.map_id

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Every coefficient word is the finite sum of all its original coloured coordinates. -/
theorem coefficientSplitWord_reconstruct (splitting : I.KSplit)
    (x : V ⊗[k] TensorPower k N A) :
    (∑ colour : Fin N → Bool,
      coefficientSplitWordToAmbient k A I V splitting colour
        (coefficientSplitAmbientToWord k A I V splitting colour x)) = x := by
  have h := congrArg
    (fun f : V ⊗[k] TensorPower k N A →ₗ[k] V ⊗[k] TensorPower k N A => f x)
    (coefficientSplitWordToAmbient_sum_comp_coefficientSplitAmbientToWord k A I V splitting N)
  simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.id_apply] using h

/-- The finite coefficient-coordinate family, with independent universes unchanged. -/
abbrev coefficientSplitWordCoordinates (N : ℕ) : Type (max u v w) :=
  ∀ colour : Fin N → Bool, V ⊗[k] splitWordTensor k A I colour

/-- The native family map collects every original arbitrary-coefficient coordinate. -/
def coefficientAmbientToSplitWordCoordinates (splitting : I.KSplit) (N : ℕ) :
    V ⊗[k] TensorPower k N A →ₗ[k] coefficientSplitWordCoordinates k A I V N :=
  LinearMap.pi (fun colour => coefficientSplitAmbientToWord k A I V splitting colour)

/-- The native finite sum reconstructs by the original coefficient and original coloured word maps. -/
def coefficientSplitWordCoordinatesToAmbient (splitting : I.KSplit) (N : ℕ) :
    coefficientSplitWordCoordinates k A I V N →ₗ[k] V ⊗[k] TensorPower k N A :=
  ∑ colour : Fin N → Bool,
    (coefficientSplitWordToAmbient k A I V splitting colour).comp (LinearMap.proj colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The full original coefficient reconstruction earns the ambient inverse identity. -/
theorem coefficientSplitWordCoordinatesToAmbient_comp_coefficientAmbientToSplitWordCoordinates
    (splitting : I.KSplit) (N : ℕ) :
    (coefficientSplitWordCoordinatesToAmbient k A I V splitting N).comp
        (coefficientAmbientToSplitWordCoordinates k A I V splitting N) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (∑ colour : Fin N → Bool,
      (coefficientSplitWordToAmbient k A I V splitting colour).comp (LinearMap.proj colour))
        (coefficientAmbientToSplitWordCoordinates k A I V splitting N x) = x
  simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    coefficientAmbientToSplitWordCoordinates, LinearMap.pi_apply] using
      (coefficientSplitWord_reconstruct k A I V splitting x)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Full original coefficient orthogonality earns the complete-family inverse identity. -/
theorem coefficientAmbientToSplitWordCoordinates_comp_coefficientSplitWordCoordinatesToAmbient
    (splitting : I.KSplit) (N : ℕ) :
    (coefficientAmbientToSplitWordCoordinates k A I V splitting N).comp
        (coefficientSplitWordCoordinatesToAmbient k A I V splitting N) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  funext target
  change coefficientSplitAmbientToWord k A I V splitting target
      ((∑ source : Fin N → Bool,
        (coefficientSplitWordToAmbient k A I V splitting source).comp (LinearMap.proj source)) x) =
      x target
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [map_sum]
  have hterm (source : Fin N → Bool) :
      coefficientSplitAmbientToWord k A I V splitting target
          (coefficientSplitWordToAmbient k A I V splitting source (x source)) =
        if source = target then x target else 0 := by
    by_cases h : source = target
    · subst source
      rw [ite_eq_left rfl]
      exact congrArg (fun f => f (x target))
        (coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient k A I V splitting target)
    · rw [ite_eq_right h]
      exact congrArg (fun f => f (x source))
        (coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient_zero
          k A I V splitting source target h)
  simp_rw [hterm]
  simp

/-- The finite coefficient-coordinate equivalence uses only the original source splitting. -/
def coefficientSplitWordCoordinatesEquiv (splitting : I.KSplit) (N : ℕ) :
    coefficientSplitWordCoordinates k A I V N ≃ₗ[k] V ⊗[k] TensorPower k N A :=
  { coefficientSplitWordCoordinatesToAmbient k A I V splitting N with
    invFun := coefficientAmbientToSplitWordCoordinates k A I V splitting N
    left_inv := fun x => congrArg (fun f => f x)
      (coefficientAmbientToSplitWordCoordinates_comp_coefficientSplitWordCoordinatesToAmbient
        k A I V splitting N)
    right_inv := fun x => congrArg (fun f => f x)
      (coefficientSplitWordCoordinatesToAmbient_comp_coefficientAmbientToSplitWordCoordinates
        k A I V splitting N) }

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The coefficient equivalence sums the exact original coefficient-word maps. -/
theorem coefficientSplitWordCoordinatesEquiv_apply (splitting : I.KSplit) (N : ℕ)
    (x : coefficientSplitWordCoordinates k A I V N) :
    coefficientSplitWordCoordinatesEquiv k A I V splitting N x =
      ∑ colour : Fin N → Bool,
        coefficientSplitWordToAmbient k A I V splitting colour (x colour) := by
  change (∑ colour : Fin N → Bool,
    (coefficientSplitWordToAmbient k A I V splitting colour).comp (LinearMap.proj colour)) x = _
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The coefficient inverse retains the original identity, projection and quotient maps. -/
theorem coefficientSplitWordCoordinatesEquiv_symm_apply (splitting : I.KSplit) (N : ℕ)
    (x : V ⊗[k] TensorPower k N A) (colour : Fin N → Bool) :
    (coefficientSplitWordCoordinatesEquiv k A I V splitting N).symm x colour =
      coefficientSplitAmbientToWord k A I V splitting colour x := rfl

end ModuleCat.Algebra.Hochschild.NonUnital
