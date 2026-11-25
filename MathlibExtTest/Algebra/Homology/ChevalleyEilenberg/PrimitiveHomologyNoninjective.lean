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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.HomologyCoalgebra
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.PrimitiveHomologyClasses
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# A genuine noninjective CE primitive/homology comparison

The rational matrix Lie algebra has `h = E11` and `e = E12`, with
`[h,e] = e`. The nonzero vector `e` is a degree-one primitive chain. The
free-module primitive concentration theorem makes its class nonzero in
homology of the actual primitive complex. In the actual CE complex it is
the negative boundary of `h ∧ e`, so its image in CE homology vanishes.
Consequently the canonical map `H(Prim CE) → Prim H(CE)` is not injective.
No kernel/homology interchange, vanishing, or nonzero certificate is an input.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Matrix TensorProduct

namespace ChevalleyEilenbergTest.PrimitiveHomologyNoninjective

abbrev L : Type := Matrix (Fin 2) (Fin 2) ℚ

local instance matrixLieRing : LieRing L := LieRing.ofAssociativeRing


def h : L := !![1, 0; 0, 0]

def e : L := !![0, 1; 0, 0]

theorem e_ne_zero : e ≠ 0 := by
  intro hz
  have hv := congrArg (fun a : L => a 0 1) hz
  norm_num [e] at hv

theorem bracket_h_e : ⁅h, e⁆ = e := by
  change h * e - e * h = e
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [h, e, Matrix.mul_apply, Fin.sum_univ_two]

def wedgeWord : ((ChevalleyEilenberg.canonicalChainData ℚ L).complex).X 2 := exteriorPower.ιMulti ℚ 2 ![h, e]

/-- The actual CE differential, with its native negative-bracket convention. -/
theorem differential_wedgeWord :
    ((ChevalleyEilenberg.canonicalChainData ℚ L).complex).d 2 1 wedgeWord = -(exteriorPower.oneEquiv ℚ L).symm e := by
  have hd := ChevalleyEilenberg.PrimitiveHomology.pairWord_differential ℚ L h e
  exact hd.trans (congrArg (fun x => -(exteriorPower.oneEquiv ℚ L).symm x) bracket_h_e)

def primitiveVector : (ChevalleyEilenberg.nativePrimitiveComplex ℚ L).X 1 :=
  (ChevalleyEilenberg.nativePrimitiveDegreeOneEquiv ℚ L).symm e

theorem primitiveVector_ne_zero : primitiveVector ≠ 0 := by
  intro hz
  have hv := congrArg (ChevalleyEilenberg.nativePrimitiveDegreeOneEquiv ℚ L) hz
  simp only [primitiveVector, LinearEquiv.apply_symm_apply, map_zero] at hv
  exact e_ne_zero hv

def primitiveCycle : (ChevalleyEilenberg.nativePrimitiveComplex ℚ L).cycles 1 :=
  ((ChevalleyEilenberg.nativePrimitiveComplex ℚ L).iCyclesIso 1 0 (by simp)
    (ChevalleyEilenberg.nativePrimitiveComplex_d_one_zero ℚ L)).inv
    primitiveVector

theorem primitiveCycle_i : (ChevalleyEilenberg.nativePrimitiveComplex ℚ L).iCycles 1 primitiveCycle = primitiveVector
  := by
  have hv := congrArg (fun f => f primitiveVector)
    ((ChevalleyEilenberg.nativePrimitiveComplex ℚ L).iCyclesIso_inv_hom_id 1 0 (by simp)
      (ChevalleyEilenberg.nativePrimitiveComplex_d_one_zero ℚ L))
  simpa only [primitiveCycle, CategoryTheory.comp_apply, CategoryTheory.id_apply] using hv

def primitiveClass : (ChevalleyEilenberg.nativePrimitiveComplex ℚ L).homology 1 :=
  (ChevalleyEilenberg.nativePrimitiveComplex ℚ L).homologyπ 1 primitiveCycle

/-- The input class is nonzero in homology of the actual primitive kernel;
freeness is earned from the native rational matrix basis. -/
theorem primitiveClass_ne_zero : primitiveClass ≠ 0 := by
  letI : IsIso ((ChevalleyEilenberg.nativePrimitiveComplex ℚ L).homologyπ 1) :=
    (ChevalleyEilenberg.nativePrimitiveComplex ℚ L).isIso_homologyπ 2 1 (by simp)
    (ChevalleyEilenberg.nativePrimitiveComplex_d_eq_zero ℚ L 2 1)
  have hi : Function.Injective ((ChevalleyEilenberg.nativePrimitiveComplex ℚ L).homologyπ 1) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  intro hz
  have hc : primitiveCycle = 0 := hi (by simpa only [primitiveClass, map_zero] using hz)
  have hv := congrArg ((ChevalleyEilenberg.nativePrimitiveComplex ℚ L).iCycles 1) hc
  rw [primitiveCycle_i, map_zero] at hv
  exact primitiveVector_ne_zero hv

/-- The actual cycle image is the negative of the actual boundary cycle. -/
theorem cycleImage_is_boundary :
    HomologicalComplex.cyclesMap (ChevalleyEilenberg.nativePrimitiveInclusion ℚ L) 1 primitiveCycle =
      -((ChevalleyEilenberg.canonicalChainData ℚ L).complex).toCycles 2 1 wedgeWord := by
  apply ((ModuleCat.mono_iff_injective (((ChevalleyEilenberg.canonicalChainData ℚ L).complex).iCycles 1)).mp
    inferInstance)
  have hi := congrArg (fun f => f primitiveCycle) (HomologicalComplex.cyclesMap_i
    (ChevalleyEilenberg.nativePrimitiveInclusion ℚ L) 1)
  simp only [CategoryTheory.comp_apply] at hi
  have hb := congrArg (fun f => f wedgeWord) (((ChevalleyEilenberg.canonicalChainData ℚ L).complex).toCycles_i 2 1)
  simp only [CategoryTheory.comp_apply] at hb
  rw [hi, primitiveCycle_i, ChevalleyEilenberg.HomologyCoalgebra.primitiveOne_inclusion]
  simp only [primitiveVector, LinearEquiv.apply_symm_apply]
  rw [map_neg, hb, differential_wedgeWord]
  exact (neg_neg (show ((ChevalleyEilenberg.canonicalChainData ℚ L).complex).X 1 from
    (exteriorPower.oneEquiv ℚ L).symm e)).symm

/-- The nonzero primitive-homology class dies in actual CE homology. -/
theorem homologyInclusion_class_zero : HomologicalComplex.homologyMap (ChevalleyEilenberg.nativePrimitiveInclusion ℚ
  L) 1 primitiveClass = 0 := by
  have hπ := congrArg (fun f => f primitiveCycle) (HomologicalComplex.homologyπ_naturality
    (ChevalleyEilenberg.nativePrimitiveInclusion ℚ L) 1)
  simp only [CategoryTheory.comp_apply] at hπ
  have hb := congrArg (fun f => f.hom wedgeWord) (((ChevalleyEilenberg.canonicalChainData ℚ
    L).complex).toCycles_comp_homologyπ 2 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at hb
  change HomologicalComplex.homologyMap (ChevalleyEilenberg.nativePrimitiveInclusion ℚ L) 1
    ((ChevalleyEilenberg.nativePrimitiveComplex ℚ L).homologyπ 1 primitiveCycle) = 0
  rw [hπ, cycleImage_is_boundary, map_neg, hb, neg_zero]

/-- The constructed canonical primitive/homology comparison kills that
nonzero input class, in its actual native graded primitive kernel. -/
theorem primitiveComparison_class_zero :
    ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) L 1 primitiveClass = 0 := by
  letI : ComonObj ((ChevalleyEilenberg.canonicalChainData ℚ L).complex) :=
    (ChevalleyEilenberg.HomologyCoalgebra.UnitComparison.chainCoalgebra ℚ L).comon
  letI : ∀ n : ℕ, IsIso (HomologicalComplex.kunnethHomologyTensorMap ((ChevalleyEilenberg.canonicalChainData ℚ
    L).complex) ((ChevalleyEilenberg.canonicalChainData ℚ L).complex) n) :=
    fun n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field ((ChevalleyEilenberg.canonicalChainData ℚ
      L).complex) ((ChevalleyEilenberg.canonicalChainData ℚ L).complex) n
  let i := (kernel.ι (HomologicalComplex.HomologyCoalgebra.homologyPrimitiveEquation
    ((ChevalleyEilenberg.canonicalChainData ℚ L).complex)
    (ChevalleyEilenberg.HomologyCoalgebra.UnitComparison.chainCoaug ℚ L))) 1
  letI : Mono i := by dsimp only [i]; infer_instance
  have hi : Function.Injective i := (ModuleCat.mono_iff_injective i).mp inferInstance
  have hm := congrFun
    (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison_inclusion (k := ℚ) L) 1
  have hv := congrArg (fun f => f primitiveClass) hm
  change i (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) L 1
    primitiveClass) = HomologicalComplex.homologyMap (ChevalleyEilenberg.nativePrimitiveInclusion ℚ L) 1
      primitiveClass at hv
  rw [homologyInclusion_class_zero] at hv
  exact hi (hv.trans i.hom.map_zero.symm)

/-- Kernels do not commute with homology even for a finite-dimensional free
rational CE complex. The actual canonical comparison is not injective. -/
theorem primitiveComparison_not_injective :
    ¬ Function.Injective
      (ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) L 1) := by
  intro hi
  have hz := hi (show ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison
      (k := ℚ) L 1 primitiveClass =
      ChevalleyEilenberg.HomologyCoalgebra.primitiveHomologyComparison (k := ℚ) L 1 0 by
    rw [primitiveComparison_class_zero, map_zero])
  exact primitiveClass_ne_zero hz

end ChevalleyEilenbergTest.PrimitiveHomologyNoninjective
