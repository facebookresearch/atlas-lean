/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationCompactSupport
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedMonoCofibration
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy
import MathlibExt.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Tactic.NormNum

/-!
# Hausdorffness of every actual simplicial realization

The original two-point finite-subcomplex separator is extended through the
actual realized-monomorphism lifting property against the derived terminal
trivial fibration of the real numbers. The public theorem applies to every
simplicial set in every universe, with no finite, countable, CW or separation
hypothesis on its realization.

The proof is the existing native-verified generic construction, moved from
its former private loop-model owner without changing its mathematical body.
-/

public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology Set Function
open scoped Simplicial TopCat.modelCategory SSet.modelCategoryQuillen unitInterval

universe u

namespace SSet

section HausdorffRealization

private abbrev realObject : TopCat.{u} := TopCat.of (ULift.{u} ℝ)

/-- The real target is contractible in the actual universe; weakness is derived. -/
private theorem realTerminal_weak :
    TopCat.weakHomotopyEquivalences (terminal.from realObject.{u}) := by
  let _ : ContractibleSpace ℝ :=
    (contractible_iff_id_nullhomotopic ℝ).mpr
      ⟨0, ⟨ContinuousMap.Homotopy.affine (ContinuousMap.id ℝ) (ContinuousMap.const ℝ 0)⟩⟩
  let _ : ContractibleSpace realObject.{u} :=
    (Homeomorph.ulift : ULift.{u} ℝ ≃ₜ ℝ).contractibleSpace
  let terminalHomeo : (⊤_ TopCat.{u}) ≃ₜ PUnit.{u + 1} :=
    TopCat.homeoOfIso (TopCat.terminalIsoPUnit.{u})
  let _ : ContractibleSpace (⊤_ TopCat.{u}) := terminalHomeo.contractibleSpace
  let f : realObject.{u} ⟶ ⊤_ TopCat.{u} := terminal.from realObject.{u}
  let e : ContinuousMap.HomotopyEquiv realObject.{u} (⊤_ TopCat.{u}) :=
    ContinuousMap.HomotopyEquiv.ofContractible
      (X := realObject.{u}) (Y := ⊤_ TopCat.{u}) f.hom
  exact TopCat.mem_of_eq_toFun (X := realObject.{u}) (Y := ⊤_ TopCat.{u})
    (f := f) e (by rw [ContinuousMap.HomotopyEquiv.ofContractible_toFun]; rfl)

/-- Actual all-space fibrancy from the native singular Kan theorem. -/
private theorem terminal_isFibrant (X : TopCat.{u}) : IsFibrant X := by
  rw [isFibrant_iff]
  rw [HomotopicalAlgebra.fibration_iff]
  change TopCat.realizedHornInclusions.{u}.rlp (terminal.from X)
  rw [TopCat.hornRLP_iff_toSSet_mem_J_rlp]
  rw [← SSet.modelCategoryQuillen.fibration_iff]
  rw [← isFibrant_iff_of_isTerminal _
    (IsTerminal.isTerminalObj TopCat.toSSet _ terminalIsTerminal)]
  exact TopCat.toSSet_obj_kanComplex X

/-- Extend the actual real function across a realized subcomplex using derived LLP data. -/
private def extendRealFunction {K : SSet.{u}} (A : K.Subcomplex)
    (f : C(SSet.toTop.obj (A : SSet.{u}), ℝ)) :
    {g : C(SSet.toTop.obj K, ℝ) //
      g.comp (SSet.toTop.map A.ι).hom = f} := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory.{u}
  let i : SSet.toTop.obj (A : SSet.{u}) ⟶ SSet.toTop.obj K := SSet.toTop.map A.ι
  let _ : Cofibration i := (cofibration_iff i).mpr
    (SSet.toTop_map_mem_realizedBoundaryLLP A.ι)
  let t : realObject.{u} ⟶ ⊤_ TopCat.{u} := terminal.from realObject.{u}
  let _ : IsFibrant realObject.{u} := terminal_isFibrant realObject.{u}
  let _ : Fibration t := by infer_instance
  let _ : WeakEquivalence t := (weakEquivalence_iff t).mpr realTerminal_weak
  let _ : HasLiftingProperty i t := ModelCategory.cm4b i t
  let up : C(ℝ, ULift.{u} ℝ) :=
    ⟨(Homeomorph.ulift : ULift.{u} ℝ ≃ₜ ℝ).symm, Homeomorph.ulift.symm.continuous_toFun⟩
  let a : SSet.toTop.obj (A : SSet.{u}) ⟶ realObject.{u} :=
    TopCat.ofHom (up.comp f)
  let b : SSet.toTop.obj K ⟶ ⊤_ TopCat.{u} := terminal.from _
  let sq : CommSq a i t b := ⟨terminal.hom_ext _ _⟩
  let l : SSet.toTop.obj K ⟶ realObject.{u} := sq.lift
  let down : C(ULift.{u} ℝ, ℝ) :=
    ⟨Homeomorph.ulift, Homeomorph.ulift.continuous_toFun⟩
  let g : C(SSet.toTop.obj K, ℝ) := down.comp l.hom
  refine ⟨g, ?_⟩
  apply ContinuousMap.ext
  intro x
  have h : l (i x) = a x := by
    simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom sq.fac_left x
  exact congrArg (fun z : realObject.{u} => z.down) h

/-- Two arbitrary original realization points have an actual continuous separating function. -/
private theorem realization_has_separator (K : SSet.{u})
    (x y : SSet.toTop.obj K) (hxy : x ≠ y) :
    ∃ f : C(SSet.toTop.obj K, ℝ), f x = 0 ∧ f y = 1 := by
  let S : Set (SSet.toTop.obj K) := {x, y}
  have hS : IsCompact S := by exact isCompact_singleton.insert x
  obtain ⟨A, hA, hsub⟩ := SSet.exists_finite_subcomplex_of_isCompact K S hS
  let _ : SSet.Finite (A : SSet.{u}) := hA
  let i : SSet.toTop.obj (A : SSet.{u}) ⟶ SSet.toTop.obj K := SSet.toTop.map A.ι
  obtain ⟨a, ha⟩ : x ∈ Set.range i := hsub (by simp [S])
  obtain ⟨b, hb⟩ : y ∈ Set.range i := hsub (by simp [S])
  have hab : a ≠ b := by
    intro h
    exact hxy (ha.symm.trans ((congrArg i h).trans hb))
  obtain ⟨f, hfa, hfb, _⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton : IsClosed ({a} : Set (SSet.toTop.obj (A : SSet.{u}))))
    (isClosed_singleton : IsClosed ({b} : Set (SSet.toTop.obj (A : SSet.{u}))))
    (Set.disjoint_singleton.mpr hab)
  let g := extendRealFunction A f
  have hg (z : SSet.toTop.obj (A : SSet.{u})) : g.val (i z) = f z :=
    DFunLike.congr_fun g.property z
  refine ⟨g.val, ?_, ?_⟩
  · rw [← ha, hg]
    exact hfa (Set.mem_singleton a)
  · rw [← hb, hg]
    exact hfb (Set.mem_singleton b)

/-- Hausdorffness is derived on the whole actual realization, not assumed from CW data. -/
theorem realization_t2Space (K : SSet.{u}) : T2Space (SSet.toTop.obj K) := by
  constructor
  intro x y hxy
  obtain ⟨f, hfx, hfy⟩ := realization_has_separator K x y hxy
  obtain ⟨U, V, hU, hV, h0, h1, hUV⟩ :=
    t2_separation (by norm_num : (0 : ℝ) ≠ 1)
  refine ⟨f ⁻¹' U, f ⁻¹' V, hU.preimage f.continuous, hV.preimage f.continuous, ?_, ?_,
    hUV.preimage f⟩
  · simpa only [Set.mem_preimage, hfx] using h0
  · simpa only [Set.mem_preimage, hfy] using h1

end HausdorffRealization

end SSet

end
