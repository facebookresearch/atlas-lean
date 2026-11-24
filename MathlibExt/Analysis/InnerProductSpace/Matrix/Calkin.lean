/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.Matrix.CStarAlgebra
public import MathlibExt.Analysis.Normed.Operator.Compact.Matrix
public import MathlibExt.Analysis.CStarAlgebra.Operator.Calkin

import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Finite Hilbert operator matrices modulo compact operators

The actual column-action star equivalence identifies compact finite blocks with
matrices of compact coefficients. The entrywise Calkin projection has exactly
this closed star ideal as its kernel. Descending coordinate recovery through the
existing compact-operator quotient gives the actual Calkin algebra of the finite
Hilbert product as the C-star matrix algebra over the coefficient Calkin algebra.

The canonical quotient carriers and norms are retained. Empty finite indices and
zero Hilbert spaces are allowed; no basis, absorption, nontriviality or norm-one
assumption is made. No Hilbert tensor or source classification is asserted.
-/

@[expose] public section

noncomputable section

universe uIndex uHilbert

variable {n : Type uIndex} [Fintype n]
variable {H : Type uHilbert} [NormedAddCommGroup H]
variable [InnerProductSpace ℂ H] [CompleteSpace H]

namespace CStarMatrix

/-- The actual Calkin projection applied to every operator coefficient. -/
def calkinMap :
    CStarMatrix n n (H →L[ℂ] H) →⋆ₙₐ[ℂ]
      CStarMatrix n n (CalkinAlgebra ℂ H) :=
  mapₙₐ (CalkinAlgebra.classStarMap (H := H)).toNonUnitalStarAlgHom

/-- Each entry is the class of the original continuous linear operator. -/
@[simp]
theorem calkinMap_apply_entry (X : CStarMatrix n n (H →L[ℂ] H)) (i j : n) :
    calkinMap (n := n) (H := H) X i j = CalkinAlgebra.classStarMap (H := H) (X i j) :=
  rfl

/-- Finite matrices of actual Calkin classes have actual operator representatives. -/
theorem calkinMap_surjective :
    Function.Surjective (calkinMap (n := n) (H := H)) := by
  classical
  intro X
  have hLift (i j : n) :
      ∃ T : H →L[ℂ] H, CalkinAlgebra.classStarMap (H := H) T = X i j :=
    CalkinAlgebra.classStarMap_surjective (H := H) (X i j)
  choose M hM using hLift
  refine ⟨CStarMatrix.ofMatrix M, ?_⟩
  apply CStarMatrix.ext
  intro i j
  change CalkinAlgebra.classStarMap (H := H) (M i j) = X i j
  exact hM i j

/-- A matrix has zero symbol exactly when every actual entry is compact. -/
theorem calkinMap_eq_zero_iff (X : CStarMatrix n n (H →L[ℂ] H)) :
    calkinMap (n := n) (H := H) X = 0 ↔ ∀ i j : n, IsCompactOperator (X i j) := by
  constructor
  · intro hX i j
    have hEntry := congrArg (fun Y : CStarMatrix n n (CalkinAlgebra ℂ H) => Y i j) hX
    have hZero : CalkinAlgebra.classStarMap (H := H) (X i j) = 0 := by
      simpa only [calkinMap_apply_entry, CStarMatrix.zero_apply] using hEntry
    exact (CalkinAlgebra.classStarMap_eq_zero_iff (H := H) (X i j)).mp hZero
  · intro hEntries
    apply CStarMatrix.ext
    intro i j
    exact (calkinMap_apply_entry X i j).trans
      ((CalkinAlgebra.classStarMap_eq_zero_iff (H := H) (X i j)).mpr (hEntries i j))

section HilbertBlock

variable [DecidableEq n]

/-- Compactness of the actual finite Hilbert block is exactly entrywise compactness. -/
theorem isCompactOperator_piLpStarAlgEquiv_iff
    (X : CStarMatrix n n (H →L[ℂ] H)) :
    IsCompactOperator (piLpStarAlgEquiv (n := n) (H := H) X) ↔
      ∀ i j : n, IsCompactOperator (X i j) := by
  have hAction : piLpStarAlgEquiv (n := n) (H := H) X =
      Matrix.toPiLpContinuousLinearMap (CStarMatrix.ofMatrix.symm X) := rfl
  rw [hAction]
  simpa only [CStarMatrix.ofMatrix_symm_apply] using
    (Matrix.isCompactOperator_toPiLpContinuousLinearMap_iff
      (CStarMatrix.ofMatrix.symm X))

/-- The actual closed compact-block ideal, pulled back along the Hilbert equivalence. -/
def compactOperatorIdeal :
    letI : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _;
    letI : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _;
    ClosedStarIdeal (CStarMatrix n n (H →L[ℂ] H)) := by
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
  exact ClosedStarIdeal.comap
    (piLpStarAlgEquiv (n := n) (H := H)).toNonUnitalStarAlgHom
    (compactEndomorphismClosedStarIdeal (H := PiLp 2 (fun _ : n => H)))

/-- Membership in the actual closed matrix ideal is the literal compact-entry predicate. -/
@[simp]
theorem mem_compactOperatorIdeal :
    letI : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _;
    letI : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _;
    ∀ X : CStarMatrix n n (H →L[ℂ] H),
      X ∈ compactOperatorIdeal (n := n) (H := H) ↔
        ∀ i j : n, IsCompactOperator (X i j) := by
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
  change ∀ X : CStarMatrix n n (H →L[ℂ] H),
    IsCompactOperator (piLpStarAlgEquiv (n := n) (H := H) X) ↔
      ∀ i j : n, IsCompactOperator (X i j)
  exact fun X => isCompactOperator_piLpStarAlgEquiv_iff X

/-- The genuine entrywise projection kernel is the actual closed compact-block ideal. -/
theorem ker_calkinMap :
    letI : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _;
    letI : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _;
    letI : PartialOrder (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrder _;
    letI : StarOrderedRing (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrderedRing _;
    ClosedStarIdeal.ker (calkinMap (n := n) (H := H)) =
      compactOperatorIdeal (n := n) (H := H) := by
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
  let : PartialOrder (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrderedRing _
  apply ClosedStarIdeal.ext
  intro X
  rw [ClosedStarIdeal.mem_ker, mem_compactOperatorIdeal]
  exact calkinMap_eq_zero_iff X

end HilbertBlock

end CStarMatrix

namespace CalkinAlgebra

variable [DecidableEq n]

open scoped NonUnitalStarSubalgebra.Quotient in
/-- Coordinate recovery followed by entrywise classes, on the existing Calkin quotient. -/
def piLpMap :
    CalkinAlgebra ℂ (PiLp 2 (fun _ : n => H)) →⋆ₙₐ[ℂ]
      CStarMatrix n n (CalkinAlgebra ℂ H) := by
  let J := compactEndomorphismClosedStarIdeal (H := PiLp 2 (fun _ : n => H))
  let : J.carrier.IsTwoSided := J.isTwoSided
  let e := CStarMatrix.piLpStarAlgEquiv (n := n) (H := H)
  let f : (PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H)) →⋆ₙₐ[ℂ]
      CStarMatrix n n (CalkinAlgebra ℂ H) :=
    (CStarMatrix.calkinMap (n := n) (H := H)).comp e.symm.toNonUnitalStarAlgHom
  have hJ : ∀ T ∈ J.carrier, f T = 0 := by
    intro T hT
    have hCompact : IsCompactOperator T := hT
    change CStarMatrix.calkinMap (n := n) (H := H) (e.symm T) = 0
    apply (CStarMatrix.calkinMap_eq_zero_iff (e.symm T)).mpr
    intro i j
    change IsCompactOperator (ContinuousLinearMap.toPiLpMatrix T i j)
    exact hCompact.toPiLpMatrix i j
  let induced := NonUnitalStarSubalgebra.Quotient.lift J.carrier f hJ
  exact
    { toFun := fun q => induced q
      map_zero' := map_zero induced
      map_add' := map_add induced
      map_mul' := map_mul induced
      map_smul' := map_smul induced
      map_star' := map_star induced }

/-- On an actual operator representative, the quotient map is the literal recovered symbol. -/
@[simp]
theorem piLpMap_classStarMap
    (T : PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H)) :
    piLpMap (n := n) (H := H) (classStarMap (H := PiLp 2 (fun _ : n => H)) T) =
      CStarMatrix.calkinMap (n := n) (H := H)
        ((CStarMatrix.piLpStarAlgEquiv (n := n) (H := H)).symm T) :=
  rfl

/-- The induced map is genuinely bijective, using actual compactness and
quotient representatives. -/
theorem piLpMap_bijective : Function.Bijective (piLpMap (n := n) (H := H)) := by
  let e := CStarMatrix.piLpStarAlgEquiv (n := n) (H := H)
  let p := CStarMatrix.calkinMap (n := n) (H := H)
  let q := classStarMap (H := PiLp 2 (fun _ : n => H))
  constructor
  · intro x y hxy
    obtain ⟨T, rfl⟩ := classStarMap_surjective (H := PiLp 2 (fun _ : n => H)) x
    obtain ⟨S, rfl⟩ := classStarMap_surjective (H := PiLp 2 (fun _ : n => H)) y
    have hImage : p (e.symm T) = p (e.symm S) := by
      simpa only [piLpMap_classStarMap] using hxy
    have hZero : p (e.symm (T - S)) = 0 := by
      rw [map_sub, map_sub, hImage, sub_self]
    have hEntries : ∀ i j : n, IsCompactOperator ((e.symm (T - S)) i j) :=
      (CStarMatrix.calkinMap_eq_zero_iff (e.symm (T - S))).mp hZero
    have hBlock : IsCompactOperator (e (e.symm (T - S))) :=
      (CStarMatrix.isCompactOperator_piLpStarAlgEquiv_iff (e.symm (T - S))).mpr hEntries
    have hCompact : IsCompactOperator (T - S) := by
      simpa only [e.apply_symm_apply] using hBlock
    have hClass : q (T - S) = 0 :=
      (classStarMap_eq_zero_iff (H := PiLp 2 (fun _ : n => H)) (T - S)).mpr hCompact
    exact sub_eq_zero.mp (by simpa only [map_sub] using hClass)
  · intro X
    obtain ⟨M, hM⟩ := CStarMatrix.calkinMap_surjective X
    refine ⟨q (e M), ?_⟩
    calc
      piLpMap (n := n) (H := H) (q (e M)) = p (e.symm (e M)) :=
        piLpMap_classStarMap (e M)
      _ = p M := congrArg (fun Y => p Y) (e.symm_apply_apply M)
      _ = X := hM

/-- The actual Calkin algebra of the finite Hilbert product, as an
operator-matrix Calkin algebra. -/
def piLpStarAlgEquiv :
    CalkinAlgebra ℂ (PiLp 2 (fun _ : n => H)) ≃⋆ₐ[ℂ]
      CStarMatrix n n (CalkinAlgebra ℂ H) :=
  StarAlgEquiv.ofBijective (piLpMap (n := n) (H := H)) piLpMap_bijective

/-- The equivalence retains the actual operator representative and recovered entry classes. -/
theorem piLpStarAlgEquiv_classStarMap
    (T : PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H)) :
    piLpStarAlgEquiv (n := n) (H := H)
        (classStarMap (H := PiLp 2 (fun _ : n => H)) T) =
      CStarMatrix.calkinMap (n := n) (H := H)
        ((CStarMatrix.piLpStarAlgEquiv (n := n) (H := H)).symm T) :=
  piLpMap_classStarMap T

/-- On an entrywise operator representative, the inverse is the class of its
actual Hilbert block. -/
theorem piLpStarAlgEquiv_symm_calkinMap (X : CStarMatrix n n (H →L[ℂ] H)) :
    (piLpStarAlgEquiv (n := n) (H := H)).symm
        (CStarMatrix.calkinMap (n := n) (H := H) X) =
      classStarMap (H := PiLp 2 (fun _ : n => H))
        (CStarMatrix.piLpStarAlgEquiv (n := n) (H := H) X) := by
  let e := CStarMatrix.piLpStarAlgEquiv (n := n) (H := H)
  let p := CStarMatrix.calkinMap (n := n) (H := H)
  apply (piLpStarAlgEquiv (n := n) (H := H)).symm_apply_eq.mpr
  rw [piLpStarAlgEquiv_classStarMap]
  exact (congrArg (fun Y => p Y) (e.symm_apply_apply X)).symm

/-- The quotient bridge preserves the actual canonical Calkin and CStarMatrix metrics. -/
theorem piLpStarAlgEquiv_isometry :
    letI : PartialOrder (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrder _;
    letI : StarOrderedRing (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrderedRing _;
    Isometry (piLpStarAlgEquiv (n := n) (H := H)) := by
  let : PartialOrder (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrderedRing _
  let e := piLpStarAlgEquiv (n := n) (H := H)
  exact NonUnitalStarAlgHom.isometry e.toNonUnitalStarAlgHom e.injective

/-- No quotient norm is replaced: this is the actual matrix operator norm of the image. -/
theorem piLpStarAlgEquiv_norm_map :
    letI : PartialOrder (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrder _;
    letI : StarOrderedRing (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrderedRing _;
    ∀ x : CalkinAlgebra ℂ (PiLp 2 (fun _ : n => H)),
      ‖piLpStarAlgEquiv (n := n) (H := H) x‖ = ‖x‖ := by
  let : PartialOrder (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrderedRing _
  let e := piLpStarAlgEquiv (n := n) (H := H)
  exact fun x : CalkinAlgebra ℂ (PiLp 2 (fun _ : n => H)) =>
    NonUnitalStarAlgHom.norm_map e.toNonUnitalStarAlgHom e.injective x

end CalkinAlgebra

end
