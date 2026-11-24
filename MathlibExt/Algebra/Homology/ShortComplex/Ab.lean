/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import MathlibExt.Algebra.Homology.Functor

/-! # Transport of actual cycle values and classes in abelian groups -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

universe s t

namespace CategoryTheory.ShortComplex

/-- A middle-coordinate equation determines the transported categorical cycle
under the canonical universe-lift comparison. -/
theorem ulift_cyclesMap_eq_of_middle_eq
    (S : ShortComplex AddCommGrpCat.{s})
    (T : ShortComplex AddCommGrpCat.{max t s}) (hT : T.LeftHomologyData)
    (φ : T ⟶ S.map AddCommGrpCat.uliftFunctor.{t, s})
    (c : hT.K) (z : S.g.hom.ker)
    (hval : φ.τ₂ (hT.i c) = ULift.up z.val) :
    (S.mapCyclesIso AddCommGrpCat.uliftFunctor.{t, s}).hom
      (cyclesMap φ (hT.cyclesIso.inv c)) =
        ULift.up (S.abCyclesIso.inv z) := by
  let U := AddCommGrpCat.uliftFunctor.{t, s}
  apply (AddCommGrpCat.mono_iff_injective (U.map S.iCycles)).mp inferInstance
  have hU := ConcreteCategory.congr_hom (S.mapCyclesIso_hom_iCycles U)
    (cyclesMap φ (hT.cyclesIso.inv c))
  have hφ := ConcreteCategory.congr_hom (cyclesMap_i φ) (hT.cyclesIso.inv c)
  have hTι := ConcreteCategory.congr_hom hT.cyclesIso_inv_comp_iCycles c
  have hz : (ULift.up z.val : U.obj S.X₂) =
      U.map S.iCycles (ULift.up (S.abCyclesIso.inv z)) :=
    (congrArg (fun x : S.X₂ => (ULift.up x : U.obj S.X₂))
      (S.abCyclesIso_inv_apply_iCycles z)).symm
  exact hU.trans (hφ.trans ((congrArg φ.τ₂ hTι).trans (hval.trans hz)))

end CategoryTheory.ShortComplex

namespace CategoryTheory.ShortComplex

/-- Transport a kernel cycle backwards along a short-complex isomorphism,
preserving its underlying value and its homology class. -/
theorem ab_cycle_transport_inv
    {S T : ShortComplex AddCommGrpCat.{s}} (e : S ≅ T) (z : T.g.hom.ker) :
    ∃ z₀ : S.g.hom.ker,
      z₀.val = e.inv.τ₂ z.val ∧
      S.homologyπ (S.abCyclesIso.inv z₀) =
        (homologyMapIso e).inv (T.homologyπ (T.abCyclesIso.inv z)) := by
  let a := cyclesMap e.inv (T.abCyclesIso.inv z)
  let z₀ := S.abCyclesIso.hom a
  have hza : S.abCyclesIso.inv z₀ = a :=
    ConcreteCategory.congr_hom S.abCyclesIso.hom_inv_id a
  have hi : S.iCycles a = e.inv.τ₂ z.val :=
    (ConcreteCategory.congr_hom (cyclesMap_i e.inv) (T.abCyclesIso.inv z)).trans
      (congrArg e.inv.τ₂ (T.abCyclesIso_inv_apply_iCycles z))
  refine ⟨z₀, ?_, ?_⟩
  · exact (S.abCyclesIso_inv_apply_iCycles z₀).symm.trans
      ((congrArg S.iCycles hza).trans hi)
  · exact (congrArg S.homologyπ hza).trans
      (ConcreteCategory.congr_hom (homologyπ_naturality e.inv) (T.abCyclesIso.inv z)).symm

end CategoryTheory.ShortComplex


-- Homology-value transport by @toskua.

namespace CategoryTheory.ShortComplex

/-- A middle-coordinate equation determines the transported native homology class,
using the same cycle and quotient as the original short complexes. -/
theorem ulift_homologyMap_eq_of_middle_eq
    (S : ShortComplex AddCommGrpCat.{s})
    (T : ShortComplex AddCommGrpCat.{max t s}) (hT : T.LeftHomologyData)
    (φ : T ⟶ S.map AddCommGrpCat.uliftFunctor.{t, s})
    (c : hT.K) (z : S.g.hom.ker)
    (hval : φ.τ₂ (hT.i c) = ULift.up z.val) :
    (S.mapHomologyIso AddCommGrpCat.uliftFunctor.{t, s}).hom
        (homologyMap φ (T.homologyπ (hT.cyclesIso.inv c))) =
      ULift.up (S.homologyπ (S.abCyclesIso.inv z)) := by
  let U := AddCommGrpCat.uliftFunctor.{t, s}
  have hπ : homologyMap φ (T.homologyπ (hT.cyclesIso.inv c)) =
      (S.map U).homologyπ (cyclesMap φ (hT.cyclesIso.inv c)) :=
    ConcreteCategory.congr_hom (homologyπ_naturality φ) (hT.cyclesIso.inv c)
  have hUπ := ConcreteCategory.congr_hom (S.homologyπ_comp_mapHomologyIso_hom U)
    (cyclesMap φ (hT.cyclesIso.inv c))
  have hc := ulift_cyclesMap_eq_of_middle_eq S T hT φ c z hval
  exact (congrArg (S.mapHomologyIso U).hom hπ).trans
    (hUπ.trans (congrArg (U.map S.homologyπ) hc))

end CategoryTheory.ShortComplex
