/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.IntervalBoundaryPoints
public import MathlibExt.Topology.Category.CGWH.IntervalCylinder
public import MathlibExt.Topology.Category.CGWH.CartesianMonoidalComputations

/-!
# Currying one original whole interval square in the native category

Only the original two compact interval coordinates are converted. The
entire active source keeps its original native topology. The square gives
a native homotopy in the interval internal Hom, and both horizontal faces
prove restriction along the WHOLE original boundary is fixed. No ordinary
product inverse or endpoint-preserving lifting witness is supplied.
-/

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra
open scoped CGWH.modelCategory

universe u v

namespace CGWH

variable {A M : CGWH.{u, v}}

private def nativeSquareCoordinates :
    C((nativeInterval.{u, v} ⊗ (A ⊗ nativeInterval.{u, v}) : CGWH.{u, v}),
      (unitInterval × unitInterval) × A) := by
  let t : C((nativeInterval.{u, v} ⊗ (A ⊗ nativeInterval.{u, v}) : CGWH.{u, v}), unitInterval) :=
    nativeIntervalClock.{u, v}.comp (ConcreteCategory.hom (C := CGWH.{u, v})
      (CartesianMonoidalCategory.snd nativeInterval.{u, v} (A ⊗ nativeInterval.{u, v}) ≫
        CartesianMonoidalCategory.snd A nativeInterval.{u, v}))
  let s : C((nativeInterval.{u, v} ⊗ (A ⊗ nativeInterval.{u, v}) : CGWH.{u, v}), unitInterval) :=
    nativeIntervalClock.{u, v}.comp (ConcreteCategory.hom (C := CGWH.{u, v})
      (CartesianMonoidalCategory.fst nativeInterval.{u, v} (A ⊗ nativeInterval.{u, v})))
  let a : C((nativeInterval.{u, v} ⊗ (A ⊗ nativeInterval.{u, v}) : CGWH.{u, v}), A) :=
    ConcreteCategory.hom (C := CGWH.{u, v})
      (CartesianMonoidalCategory.snd nativeInterval.{u, v} (A ⊗ nativeInterval.{u, v}) ≫
        CartesianMonoidalCategory.fst A nativeInterval.{u, v})
  exact (t.prodMk s).prodMk a

private theorem nativeSquareCoordinates_apply
    (s t : nativeInterval.{u, v}) (a : A) :
    nativeSquareCoordinates (tensorMk s (tensorMk a t)) =
      ((nativeIntervalClock.{u, v} t, nativeIntervalClock.{u, v} s), a) := by
  change ((nativeIntervalClock.{u, v}
      ((CartesianMonoidalCategory.snd nativeInterval.{u, v} (A ⊗ nativeInterval.{u, v}) ≫
        CartesianMonoidalCategory.snd A nativeInterval.{u, v}) (tensorMk s (tensorMk a t))),
    nativeIntervalClock.{u, v} (CartesianMonoidalCategory.fst nativeInterval.{u, v}
      (A ⊗ nativeInterval.{u, v}) (tensorMk s (tensorMk a t)))),
    (CartesianMonoidalCategory.snd nativeInterval.{u, v} (A ⊗ nativeInterval.{u, v}) ≫
      CartesianMonoidalCategory.fst A nativeInterval.{u, v}) (tensorMk s (tensorMk a t))) = _
  simp only [ConcreteCategory.comp_apply, tensorMk_fst, tensorMk_snd]

private def nativeSquareEvaluation (K : C((unitInterval × unitInterval) × A, M)) :
    nativeInterval.{u, v} ⊗ (A ⊗ nativeInterval.{u, v}) ⟶ M :=
  ConcreteCategory.ofHom (K.comp nativeSquareCoordinates)

private theorem nativeSquareEvaluation_apply
    (K : C((unitInterval × unitInterval) × A, M))
    (s t : nativeInterval.{u, v}) (a : A) :
    nativeSquareEvaluation K (tensorMk s (tensorMk a t)) =
      K ((nativeIntervalClock.{u, v} t, nativeIntervalClock.{u, v} s), a) :=
  congrArg K (nativeSquareCoordinates_apply s t a)

/-- The actual original whole square, curried over its original inner
interval and retaining every original active-source point. -/
public def nativeSquareCurry (K : C((unitInterval × unitInterval) × A, M)) :
    A ⊗ nativeInterval.{u, v} ⟶ (ihom nativeInterval.{u, v}).obj M :=
  MonoidalClosed.curry (nativeSquareEvaluation K)

private theorem nativeSquareCurry_uncurry_apply_computed
    (K : C((unitInterval × unitInterval) × A, M))
    (s t : nativeInterval.{u, v}) (a : A) :
    MonoidalClosed.uncurry (nativeSquareCurry K) (tensorMk s (tensorMk a t)) =
      K ((nativeIntervalClock.{u, v} t, nativeIntervalClock.{u, v} s), a) := by
  unfold nativeSquareCurry
  exact (ConcreteCategory.congr_hom (MonoidalClosed.uncurry_curry (nativeSquareEvaluation K))
      (tensorMk s (tensorMk a t))).trans (nativeSquareEvaluation_apply K s t a)

/-- The complete native uncurrying has its SAME original two-clock value. -/
public theorem nativeSquareCurry_uncurry_apply
    (K : C((unitInterval × unitInterval) × A, M))
    (s t : nativeInterval.{u, v}) (a : A) :
    MonoidalClosed.uncurry (nativeSquareCurry K) (tensorMk s (tensorMk a t)) =
      K ((nativeIntervalClock.{u, v} t, nativeIntervalClock.{u, v} s), a) :=
  nativeSquareCurry_uncurry_apply_computed K s t a

/-- The initial whole square face gives the original native homotopy map. -/
public theorem nativeSquareCurry_zero
    (K : C((unitInterval × unitInterval) × A, M))
    (s₀ : A ⟶ (ihom nativeInterval.{u, v}).obj M)
    (h₀ : ∀ s a, K ((0, s), a) = MonoidalClosed.uncurry s₀
      (tensorMk (nativeIntervalHomeomorph.{u, v}.symm s) a)) :
    nativeIntervalCylinderEndpoint A 0 ≫ nativeSquareCurry K = s₀ := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left]
  apply ConcreteCategory.hom_ext
  intro z
  let s := CartesianMonoidalCategory.fst nativeInterval.{u, v} A z
  let a := CartesianMonoidalCategory.snd nativeInterval.{u, v} A z
  have hz : tensorMk s a = z := tensorMk_fst_snd z
  have hv :
      ((nativeInterval.{u, v} ◁ nativeIntervalCylinderEndpoint A 0) ≫
        MonoidalClosed.uncurry (nativeSquareCurry K)) (tensorMk s a) =
      MonoidalClosed.uncurry s₀ (tensorMk s a) := by
    rw [ConcreteCategory.comp_apply, tensorMk_whiskerLeft,
      nativeIntervalCylinderEndpoint_apply, nativeSquareCurry_uncurry_apply,
      nativeIntervalClock_zero.{u, v}]
    exact (h₀ (nativeIntervalClock.{u, v} s) a).trans
      (congrArg (fun t => MonoidalClosed.uncurry s₀ (tensorMk t a))
        (nativeIntervalHomeomorph_symm_clock.{u, v} s))
  exact (congrArg (fun q => ((nativeInterval.{u, v} ◁ nativeIntervalCylinderEndpoint A 0) ≫
    MonoidalClosed.uncurry (nativeSquareCurry K)) q) hz.symm).trans
      (hv.trans (congrArg (fun q => MonoidalClosed.uncurry s₀ q) hz))

/-- The terminal whole square face gives the original second native map. -/
public theorem nativeSquareCurry_one
    (K : C((unitInterval × unitInterval) × A, M))
    (s₁ : A ⟶ (ihom nativeInterval.{u, v}).obj M)
    (h₁ : ∀ s a, K ((1, s), a) = MonoidalClosed.uncurry s₁
      (tensorMk (nativeIntervalHomeomorph.{u, v}.symm s) a)) :
    nativeIntervalCylinderEndpoint A 1 ≫ nativeSquareCurry K = s₁ := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left]
  apply ConcreteCategory.hom_ext
  intro z
  let s := CartesianMonoidalCategory.fst nativeInterval.{u, v} A z
  let a := CartesianMonoidalCategory.snd nativeInterval.{u, v} A z
  have hz : tensorMk s a = z := tensorMk_fst_snd z
  have hv :
      ((nativeInterval.{u, v} ◁ nativeIntervalCylinderEndpoint A 1) ≫
        MonoidalClosed.uncurry (nativeSquareCurry K)) (tensorMk s a) =
      MonoidalClosed.uncurry s₁ (tensorMk s a) := by
    rw [ConcreteCategory.comp_apply, tensorMk_whiskerLeft,
      nativeIntervalCylinderEndpoint_apply, nativeSquareCurry_uncurry_apply,
      nativeIntervalClock_one.{u, v}]
    exact (h₁ (nativeIntervalClock.{u, v} s) a).trans
      (congrArg (fun t => MonoidalClosed.uncurry s₁ (tensorMk t a))
        (nativeIntervalHomeomorph_symm_clock.{u, v} s))
  exact (congrArg (fun q => ((nativeInterval.{u, v} ◁ nativeIntervalCylinderEndpoint A 1) ≫
    MonoidalClosed.uncurry (nativeSquareCurry K)) q) hz.symm).trans
      (hv.trans (congrArg (fun q => MonoidalClosed.uncurry s₁ q) hz))

/-- BOTH horizontal square faces fix restriction along the WHOLE actual
boundary, as an equality of complete native mapping-space maps. -/
public theorem nativeSquareCurry_over_boundary
    (K : C((unitInterval × unitInterval) × A, M))
    (s₀ : A ⟶ (ihom nativeInterval.{u, v}).obj M)
    (hsource : ∀ t a, K ((t, 0), a) = MonoidalClosed.uncurry s₀
      (tensorMk (nativeIntervalHomeomorph.{u, v}.symm 0) a))
    (htarget : ∀ t a, K ((t, 1), a) = MonoidalClosed.uncurry s₀
      (tensorMk (nativeIntervalHomeomorph.{u, v}.symm 1) a)) :
    nativeSquareCurry K ≫ (MonoidalClosed.pre nativeIntervalBoundary.{u, v}).app M =
      CartesianMonoidalCategory.fst A nativeInterval.{u, v} ≫ s₀ ≫
        (MonoidalClosed.pre nativeIntervalBoundary.{u, v}).app M := by
  rw [← Category.assoc]
  apply nativeIntervalBoundary_pre_ext.{u, v} (nativeSquareCurry K)
    (CartesianMonoidalCategory.fst A nativeInterval.{u, v} ≫ s₀)
  all_goals
    rw [MonoidalClosed.uncurry_natural_left]
    apply ConcreteCategory.hom_ext
    intro z
    let q := CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v}) (A ⊗ nativeInterval.{u, v}) z
    let a := CartesianMonoidalCategory.fst A nativeInterval.{u, v}
      (CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v}) (A ⊗ nativeInterval.{u, v}) z)
    let t := CartesianMonoidalCategory.snd A nativeInterval.{u, v}
      (CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, v}) (A ⊗ nativeInterval.{u, v}) z)
    have hz : tensorMk q (tensorMk a t) = z := by
      rw [tensorMk_fst_snd]
      exact tensorMk_fst_snd z
  · have hv :
        ((nativeIntervalEndpoint.{u, v} 0 ▷ (A ⊗ nativeInterval.{u, v})) ≫
          MonoidalClosed.uncurry (nativeSquareCurry K)) (tensorMk q (tensorMk a t)) =
        ((nativeIntervalEndpoint.{u, v} 0 ▷ (A ⊗ nativeInterval.{u, v})) ≫
          (nativeInterval.{u, v} ◁ CartesianMonoidalCategory.fst A nativeInterval.{u, v}) ≫
            MonoidalClosed.uncurry s₀) (tensorMk q (tensorMk a t)) := by
      rw [ConcreteCategory.comp_apply, tensorMk_whiskerRight,
        nativeSquareCurry_uncurry_apply, nativeIntervalClock_zero.{u, v}]
      rw [ConcreteCategory.comp_apply, tensorMk_whiskerRight,
        ConcreteCategory.comp_apply, tensorMk_whiskerLeft, tensorMk_fst,
        nativeIntervalEndpoint_zero_apply.{u, v}]
      exact hsource (nativeIntervalClock.{u, v} t) a
    exact (congrArg (fun q => ((nativeIntervalEndpoint.{u, v} 0 ▷ (A ⊗ nativeInterval.{u, v})) ≫
      MonoidalClosed.uncurry (nativeSquareCurry K)) q) hz.symm).trans
        (hv.trans (congrArg (fun q => ((nativeIntervalEndpoint.{u, v} 0 ▷ (A ⊗ nativeInterval.{u, v})) ≫
          (nativeInterval.{u, v} ◁ CartesianMonoidalCategory.fst A nativeInterval.{u, v}) ≫
            MonoidalClosed.uncurry s₀) q) hz))
  · have hv :
        ((nativeIntervalEndpoint.{u, v} 1 ▷ (A ⊗ nativeInterval.{u, v})) ≫
          MonoidalClosed.uncurry (nativeSquareCurry K)) (tensorMk q (tensorMk a t)) =
        ((nativeIntervalEndpoint.{u, v} 1 ▷ (A ⊗ nativeInterval.{u, v})) ≫
          (nativeInterval.{u, v} ◁ CartesianMonoidalCategory.fst A nativeInterval.{u, v}) ≫
            MonoidalClosed.uncurry s₀) (tensorMk q (tensorMk a t)) := by
      rw [ConcreteCategory.comp_apply, tensorMk_whiskerRight,
        nativeSquareCurry_uncurry_apply, nativeIntervalClock_one.{u, v}]
      rw [ConcreteCategory.comp_apply, tensorMk_whiskerRight,
        ConcreteCategory.comp_apply, tensorMk_whiskerLeft, tensorMk_fst,
        nativeIntervalEndpoint_one_apply.{u, v}]
      exact htarget (nativeIntervalClock.{u, v} t) a
    exact (congrArg (fun q => ((nativeIntervalEndpoint.{u, v} 1 ▷ (A ⊗ nativeInterval.{u, v})) ≫
      MonoidalClosed.uncurry (nativeSquareCurry K)) q) hz.symm).trans
        (hv.trans (congrArg (fun q => ((nativeIntervalEndpoint.{u, v} 1 ▷ (A ⊗ nativeInterval.{u, v})) ≫
          (nativeInterval.{u, v} ◁ CartesianMonoidalCategory.fst A nativeInterval.{u, v}) ≫
            MonoidalClosed.uncurry s₀) q) hz))

end CGWH

end
