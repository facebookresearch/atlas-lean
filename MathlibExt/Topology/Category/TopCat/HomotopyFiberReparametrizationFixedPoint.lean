/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBasepointChange

/-!
# Constant full paths are fixed by the constructed fiber reparameterization

The actual affine fiber homotopy retains the target total and point-source
coordinates. If its target carries a whole constant path, every affine path
parameter has the same value. The resulting equality fixes the actual full
homotopy-fiber point at every homotopy time.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

namespace TopCat

/-- The constructed full-fiber reparameterization fixes an image whose entire
path coordinate is the constant path. No source-image equality is assumed. -/
theorem homotopyFiberReparamHomotopy_fixed_of_path_eq_const
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (source target : A ⟶ homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1)
    (htotal : source ≫ homotopyFiberToTotal f b =
      target ≫ homotopyFiberToTotal f b)
    (hpath : ∀ (a : A) (t : TopCat.I.{u}),
      (source ≫ homotopyFiberPath f b) a t =
        (target ≫ homotopyFiberPath f b) a
          ((TopCat.I.homeomorph.{u}).symm (r ((TopCat.I.homeomorph.{u}) t))))
    (a : A)
    (hconst : homotopyFiberPath f b (target a) = ContinuousMap.const TopCat.I.{u} b)
    (s : unitInterval) :
    homotopyFiberReparamHomotopy f b source target r hr hr0 hr1 htotal hpath
      (s, a) = target a := by
  let theta := homotopyFiberReparamHomotopy f b source target r hr hr0 hr1 htotal hpath
  let T : TopCat.{u} := TopCat.of PUnit.{u + 1}
  let D : TopCat.{u} := TopCat.of (unitInterval × A)
  let c : T ⟶ homotopyFiber f b := TopCat.const (theta (s, a))
  let d : T ⟶ homotopyFiber f b := TopCat.const (target a)
  have hvalue : ∀ t : TopCat.I.{u}, homotopyFiberPath f b (target a) t = b := by
    intro t
    exact congrArg (fun q : pathObject B => q t) hconst
  have hcd : c = d := by
    apply homotopyPullback_hom_ext
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro _
      change
        (((pullback.lift _ _ _ : D ⟶ homotopyFiber f b) ≫
            pullback.fst (Limits.prod.map f (TopCat.const (X := T) b))
              (pathEndpoints B)) ≫ Limits.prod.fst) (s, a) =
          homotopyFiberToTotal f b (target a)
      rw [pullback.lift_fst, Limits.prod.lift_fst]
      rfl
    · exact TopCat.isTerminalPUnit.hom_ext _ _
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro _
      apply ContinuousMap.ext
      intro t
      change
        ((pullback.lift _ _ _ : D ⟶ homotopyFiber f b) ≫
          pullback.snd (Limits.prod.map f (TopCat.const (X := T) b))
            (pathEndpoints B)) (s, a) t =
          homotopyFiberPath f b (target a) t
      rw [pullback.lift_snd]
      change homotopyFiberPath f b (target a) _ =
        homotopyFiberPath f b (target a) t
      exact (hvalue _).trans (hvalue t).symm
  exact ConcreteCategory.congr_hom hcd (PUnit.unit : PUnit.{u + 1})

end TopCat

end
