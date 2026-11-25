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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.PrimitiveProjective
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniverseHomologyCoalgebra
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Lie vectors as primitive homology classes

A Lie vector defines a cycle and a homology class in degree one of the primitive
Chevalley–Eilenberg complex. This class map is injective when the underlying ground-ring
module is projective.

The class of a bracket maps to zero in Chevalley–Eilenberg homology because it is a negative
boundary of a two-vector wedge. Over a field, a nonzero bracket therefore makes the canonical
primitive-homology comparison noninjective. Ring and Lie carrier universes remain independent.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Matrix

namespace ChevalleyEilenberg.PrimitiveHomology

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]


/-- The Lie vector, in the degree-one primitive kernel. -/
def vector : L →ₗ[R] (nativePrimitiveComplex R L).X 1 := (nativePrimitiveDegreeOneEquiv R L).symm.toLinearMap

/-- The cycle corresponding to a degree-one primitive vector. -/
def cycle : L →ₗ[R] (nativePrimitiveComplex R L).cycles 1 :=
  (((nativePrimitiveComplex R L).iCyclesIso 1 0 (by simp) (nativePrimitiveComplex_d_one_zero R L)).inv).hom.comp
    (vector R L)

/-- The primitive homology class of the Lie vector. -/
def classMap : L →ₗ[R] (nativePrimitiveComplex R L).homology 1 :=
  ((nativePrimitiveComplex R L).homologyπ 1).hom.comp (cycle R L)

theorem cycle_i (x : L) : (nativePrimitiveComplex R L).iCycles 1 (cycle R L x) = vector R L x := by
  have h := congrArg (fun f => f (vector R L x))
    ((nativePrimitiveComplex R L).iCyclesIso_inv_hom_id 1 0 (by simp) (nativePrimitiveComplex_d_one_zero R L))
  simpa only [cycle, LinearMap.comp_apply, CategoryTheory.comp_apply,
    CategoryTheory.id_apply] using h

/-- The coordinate bridge retains precisely the exterior generator. -/
theorem vector_inclusion (x : L) :
    ((nativePrimitiveInclusion R L).f 1).hom (vector R L x) = (exteriorPower.oneEquiv R L).symm x := by
  apply (exteriorPower.oneEquiv R L).injective
  rw [LinearEquiv.apply_symm_apply]
  change nativePrimitiveDegreeOneEquiv R L
    ((nativePrimitiveDegreeOneEquiv R L).symm x) = x
  exact LinearEquiv.apply_symm_apply _ _

/-- Projectivity makes this original-Lie-vector class map injective. -/
theorem classMap_injective [Module.Projective R L] : Function.Injective (classMap R L) := by
  letI : IsIso ((nativePrimitiveComplex R L).homologyπ 1) :=
    (nativePrimitiveComplex R L).isIso_homologyπ 2 1 (by simp)
      (nativePrimitiveComplex_d_eq_zero_of_projective R L 2 1)
  have hπ : Function.Injective ((nativePrimitiveComplex R L).homologyπ 1) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hc : Function.Injective
      ((nativePrimitiveComplex R L).iCyclesIso 1 0 (by simp) (nativePrimitiveComplex_d_one_zero R L)).inv :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  exact hπ.comp (hc.comp (nativePrimitiveDegreeOneEquiv R L).symm.injective)

/-- The CE two-vector word; no basis or freeness premise is needed. -/
def pairWord (x y : L) : ((canonicalChainData R L).complex).X 2 := exteriorPower.ιMulti R 2 ![x, y]

/-- The CE sign is `d(x ∧ y) = -[x,y]`. -/
theorem pairWord_differential (x y : L) :
    ((canonicalChainData R L).complex).d 2 1 (pairWord R L x y) = -(exteriorPower.oneEquiv R L).symm ⁅x, y⁆ := by
  rw [ChainData.complex_d_succ]
  apply Subtype.ext
  change (differential R L 1 (pairWord R L x y) : ExteriorAlgebra R L) = _
  have hd := differential_coe R L 1 (show ⋀[R]^2 L from pairWord R L x y)
  exact hd.trans (by
    simp only [pairWord, exteriorPower.ιMulti_apply_coe,
    exteriorPower.oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, Matrix.cons_val_zero, Matrix.tail_cons,
      Matrix.cons_val_one, mul_one]
    have hι : (((exteriorPower.ιMulti R 1) (fun _ => ⁅x, y⁆) : ⋀[R]^1 L) :
        ExteriorAlgebra R L) = ExteriorAlgebra.ι R ⁅x, y⁆ := by
      simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
        ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    exact (boundary_ι_mul_ι R L x y).trans
      (congrArg Neg.neg hι).symm)

/-- The image cycle of a bracket is the negative of the boundary cycle. -/
theorem bracket_cycle_is_boundary (x y : L) :
    HomologicalComplex.cyclesMap (nativePrimitiveInclusion R L) 1 (cycle R L ⁅x, y⁆) =
      -((canonicalChainData R L).complex).toCycles 2 1 (pairWord R L x y) := by
  apply ((ModuleCat.mono_iff_injective (((canonicalChainData R L).complex).iCycles 1)).mp inferInstance)
  have hi := congrArg (fun f => f (cycle R L ⁅x, y⁆))
    (HomologicalComplex.cyclesMap_i (nativePrimitiveInclusion R L) 1)
  simp only [CategoryTheory.comp_apply] at hi
  have hb := congrArg (fun f => f (pairWord R L x y)) (((canonicalChainData R L).complex).toCycles_i 2 1)
  simp only [CategoryTheory.comp_apply] at hb
  rw [hi, cycle_i, vector_inclusion]
  rw [map_neg, hb, pairWord_differential]
  exact (neg_neg (show ((canonicalChainData R L).complex).X 1 from
    (exteriorPower.oneEquiv R L).symm ⁅x, y⁆)).symm

/-- The CE homology image of every bracket's primitive class is zero. -/
theorem homologyInclusion_bracket_zero (x y : L) :
    HomologicalComplex.homologyMap (nativePrimitiveInclusion R L) 1 (classMap R L ⁅x, y⁆) = 0 := by
  have hπ := congrArg (fun f => f (cycle R L ⁅x, y⁆))
    (HomologicalComplex.homologyπ_naturality (nativePrimitiveInclusion R L) 1)
  simp only [CategoryTheory.comp_apply] at hπ
  have hb := congrArg (fun f => f.hom (pairWord R L x y))
    (((canonicalChainData R L).complex).toCycles_comp_homologyπ 2 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] at hb
  change HomologicalComplex.homologyMap (nativePrimitiveInclusion R L) 1
    ((nativePrimitiveComplex R L).homologyπ 1 (cycle R L ⁅x, y⁆)) = 0
  rw [hπ, bracket_cycle_is_boundary, map_neg, hb, neg_zero]

section Field

variable {k : Type u} [Field k]
variable (V : Type v) [LieRing V] [LieAlgebra k V]

open scoped ModuleCat.UniverseTensor
local instance : HasFiniteBiproducts (ModuleCat.{max u v} k) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u v} k)
/-- The canonical closed module tensor structure at the carrier height. -/
local instance primitiveHomologyClosed : MonoidalClosed (ModuleCat.{max u v} k) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := k)

/-- The original-field primitive comparison kills every bracket class. -/
theorem comparison_bracket_zero (x y : V) :
    UniverseHomologyCoalgebra.primitiveHomologyComparison k V 1
      (classMap k V ⁅x, y⁆) = 0 := by
  letI : ComonObj ((canonicalChainData k V).complex :
      ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) :=
    nativeComonObj k V
  let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
    (canonicalChainData k V).complex
  letI : ComonObj C := nativeComonObj k V
  let η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C :=
    nativeComplexCoaug k V
  let i := (kernel.ι (HomologicalComplex.UniverseKunneth.homologyPrimitiveEquation.{u,v} C η)) 1
  let φ := HomologicalComplex.UniverseKunneth.homologyPrimitiveEquation.{u,v} C η
  letI : Mono (kernel.ι φ) := inferInstance
  letI : Mono i := by
    change Mono ((kernel.ι φ) 1)
    exact GradedObject.mono_kernel_component φ 1
  have hm : Mono i := by
    change Mono ((kernel.ι φ) 1)
    exact GradedObject.mono_kernel_component φ 1
  have hi : Function.Injective i := (ModuleCat.mono_iff_injective i).mp hm
  have h := congrFun (UniverseHomologyCoalgebra.primitiveHomologyComparison_inclusion k V) 1
  have hx := congrArg (fun f => f (classMap k V ⁅x, y⁆)) h
  change i (UniverseHomologyCoalgebra.primitiveHomologyComparison k V 1
    (classMap k V ⁅x, y⁆)) =
      HomologicalComplex.homologyMap (nativePrimitiveInclusion k V) 1
        (classMap k V ⁅x, y⁆) at hx
  rw [homologyInclusion_bracket_zero] at hx
  have hz := i.hom.map_zero
  exact hi (hx.trans hz.symm)

/-- A nonzero bracket supplies a obstruction to injectivity of the canonical comparison. -/
theorem comparison_not_injective_of_bracket (x y : V) (hxy : ⁅x, y⁆ ≠ 0) :
    ¬ Function.Injective (UniverseHomologyCoalgebra.primitiveHomologyComparison k V 1) := by
  intro h
  have hz := h (show UniverseHomologyCoalgebra.primitiveHomologyComparison k V 1
      (classMap k V ⁅x, y⁆) =
        UniverseHomologyCoalgebra.primitiveHomologyComparison k V 1 0 by
    rw [comparison_bracket_zero, map_zero])
  have hclass : classMap k V ⁅x, y⁆ = classMap k V 0 :=
    hz.trans (classMap k V).map_zero.symm
  exact hxy ((classMap_injective k V) hclass)

end Field

end ChevalleyEilenberg.PrimitiveHomology
