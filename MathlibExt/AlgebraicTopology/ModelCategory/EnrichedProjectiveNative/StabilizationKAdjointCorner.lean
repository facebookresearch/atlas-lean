/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Limits.ArrowFunctorCornerIso
import MathlibExt.Topology.Category.PointedCGWH.NativeMappingCornerFactor

/-!
# All original evaluated stabilization corners of K-right maps are weak

The complete current native stabilization mapping natural isomorphism
transports both source and target maps of the original strict corner.
Both supplied normalized corner projections and their entire Arrow map
are retained. No global shift or relative-alpha weakness is an input.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.EnrichedFunctorMapping
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B₀ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  (s : NativeStabilizationFamily.{u, v} I L)

/-- Original K lifting gives weakness of the whole normalized
evaluated corner at every original family label. The caller supplies
its actual two-leg pullback and its actual entire corner map. -/
theorem adjointCorner_weak_of_right
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (p : X ⟶ Y) (hp : (generators s).rlp p) (l : L)
    {P : PointedCGWH.{u, v}}
    (fst : P ⟶ (ihom (s.coefficient l)).obj (X.toEnrichedFunctor.obj (s.target l)))
    (snd : P ⟶ Y.toEnrichedFunctor.obj (s.source l))
    (pb : IsPullback fst snd
      ((ihom (s.coefficient l)).map (component p (s.target l))) (adjoint s l Y))
    (φ : X.toEnrichedFunctor.obj (s.source l) ⟶ P)
    (hφ₁ : φ ≫ fst = adjoint s l X) (hφ₂ : φ ≫ snd = component p (s.source l)) :
    weakEquivalences PointedCGWH.{u, v} φ := by
  let e := CurrentFree.stabilizationMappingNatIso
    (s.source l) (s.target l) (s.coefficient l) (s.inclusion l)
  let c := PointedCGWH.NativeMappingCorner.square (stabilization s l) p
  let comparison : Arrow.mk c.π ≅ Arrow.mk φ :=
    ArrowFunctorCornerIso.arrowIso e p c.fst c.snd fst snd c.isPullback pb
      c.π φ c.π_fst c.π_snd hφ₁ hφ₂
  exact ((weakEquivalences PointedCGWH.{u, v}).arrow_mk_iso_iff comparison).mp
    (stabilizationCorner_weak s p hp l)

/-- The actual canonical normalized pullback retains both literal
projections and the original evaluated source component. -/
theorem adjointPullbackCorner_weak
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (p : X ⟶ Y) (hp : (generators s).rlp p) (l : L) :
    weakEquivalences PointedCGWH.{u, v}
      (pullback.lift (adjoint s l X) (component p (s.source l))
        (CurrentFree.adjoint_naturality
          (s.source l) (s.target l) (s.coefficient l) (s.inclusion l) p).symm) :=
  adjointCorner_weak_of_right s p hp l
    (pullback.fst ((ihom (s.coefficient l)).map (component p (s.target l))) (adjoint s l Y))
    (pullback.snd ((ihom (s.coefficient l)).map (component p (s.target l))) (adjoint s l Y))
    (IsPullback.of_hasPullback _ _) _
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
