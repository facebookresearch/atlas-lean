/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import
  MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientLongExact

/-! # Original-cochain and mapped-boundary consumers -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe v z w

namespace ContinuousCohomology.Tests

/-- The leading zero really gives injection on the existing H0 classes. -/
theorem initial_cohomology_injection {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact.{v, w} S)
    (x y : (discreteCoefficientCohomologyFunctor.{v, w} G 0).obj S.X₁)
    (h : (discreteCoefficientCohomologyFunctor.{v, w} G 0).map S.f x =
      (discreteCoefficientCohomologyFunctor.{v, w} G 0).map S.f y) : x = y :=
  ((AddCommGrpCat.mono_iff_injective _).mp
    (discreteCoefficient_cohomology_mono_zero.{v, w} S hS)) h

/-- A genuine original continuous inhomogeneous kernel cochain has a unique original lift. -/
theorem original_inhomogeneous_kernel_lift {G : ProfiniteGrp.{v}}
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G))
    (hS : DiscreteCoefficientExact.{v, w} S) (n : ℕ)
    (σ : C(Fin n → G, inhomogeneousOriginalTopRep.{0, v, w} G S.X₂))
    (hσ : ∀ t, discreteCoefficientHom.{v, w} S.g (σ t) = 0) :
    ∃! b : C(Fin n → G, inhomogeneousOriginalTopRep.{0, v, w} G S.X₁),
      ∀ t, discreteCoefficientHom.{v, w} S.f (b t) = σ t := by
  let c := (discreteCoefficientInhomogeneousEquiv.{v, w} G S.X₂ n).symm σ
  have he (t : Fin n → G) :
      discreteCoefficientInhomogeneousEquiv.{v, w} G S.X₂ n c t = σ t :=
    congrArg (fun f => f t)
      ((discreteCoefficientInhomogeneousEquiv.{v, w} G S.X₂ n).apply_symm_apply σ)
  have hc : ((discreteCoefficientCochainFunctor.{v, w} G).map S.g).f n c = 0 := by
    apply (discreteCoefficientInhomogeneousEquiv.{v, w} G S.X₃ n).injective
    apply ContinuousMap.ext
    intro t
    have hz : (0 : C(Fin n → G, inhomogeneousOriginalTopRep.{0, v, w} G S.X₃)) =
        discreteCoefficientInhomogeneousEquiv.{v, w} G S.X₃ n 0 :=
      (discreteCoefficientInhomogeneousEquiv.{v, w} G S.X₃ n).map_zero.symm
    exact (discreteCoefficientInhomogeneousEquiv_map.{v, w} S.g n c t).trans
      ((congrArg (discreteCoefficientHom.{v, w} S.g) (he t)).trans
        ((hσ t).trans (congrArg (fun q => q t) hz)))
  obtain ⟨b, hb⟩ := discreteCoefficientCochain_lift_kernel.{v, w}
    S.f S.g hS.2.1 n c hc
  have hbt (t : Fin n → G) :
      discreteCoefficientHom.{v, w} S.f
        (discreteCoefficientInhomogeneousEquiv.{v, w} G S.X₁ n b t) = σ t :=
    (discreteCoefficientInhomogeneousEquiv_map.{v, w} S.f n b t).symm.trans
      ((congrArg (fun q => discreteCoefficientInhomogeneousEquiv.{v, w}
        G S.X₂ n q t) hb).trans (he t))
  refine ⟨discreteCoefficientInhomogeneousEquiv.{v, w} G S.X₁ n b, hbt, ?_⟩
  intro b' hb'
  apply ContinuousMap.ext
  intro t
  exact hS.1 ((hb' t).trans (hbt t).symm)

set_option maxHeartbeats 2000000 in
-- The fully typed one-lift boundary consumer reached 800000 heartbeats in v26.
/-- The actual native group map sends a boundary value to the corresponding target boundary.
Both smaller coefficient models receive exactly one actual common lift. -/
theorem native_group_mapped_boundary
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {S : ShortComplex (DiscreteContAction (TopModuleCat.{max v w} ℤ) G)}
    {T : ShortComplex (DiscreteContAction (TopModuleCat.{max z w} ℤ) H)}
    (hS : DiscreteCoefficientExact.{v, w} S) (hT : DiscreteCoefficientExact.{z, w} T)
    {φ : H →ₜ* G} (f : DiscreteCoefficientNativeGroupHom.{v, z, w} S T φ) (n : ℕ) :
    let S' : ShortComplex (DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G) :=
      S.map (discreteCoefficientULiftFunctor.{v, z, w} G)
    let T' : ShortComplex (DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H) :=
      T.map (discreteCoefficientULiftFunctor.{z, v, w} H)
    let hS' : DiscreteCoefficientExact.{v, max z w} S' :=
      discreteCoefficientULiftFunctor_exact.{v, z, w} S hS
    let hT' : DiscreteCoefficientExact.{z, max v w} T' :=
      discreteCoefficientULiftFunctor_exact.{z, v, w} T hT
    let f' : DiscreteCoefficientGroupHom.{v, z, w} S' T' φ :=
      discreteCoefficientNativeGroupHom_ulift.{v, z, w} f
    ∀ (x : (discreteCoefficientCohomologyFunctor.{v, max z w} G n).obj S'.X₃)
      (y : (discreteCoefficientCohomologyFunctor.{v, max z w} G (n + 1)).obj S'.X₁),
      discreteCoefficientConnecting.{v, max z w} S' hS' n x = y →
        discreteCoefficientConnecting.{z, max v w} T' hT' n
          (discreteCoefficientForget.{max v (max z w)}.map
            (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f'.τ₃ n) x) =
        discreteCoefficientForget.{max v (max z w)}.map
          (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f'.τ₁ (n + 1)) y := by
  intro S' T' hS' hT' f' x y hxy
  have h := congrArg (fun m => m x)
    (discreteCoefficientConnecting_group_naturality.{v, z, w} hS' hT' f' n)
  exact h.symm.trans (congrArg
    (discreteCoefficientForget.{max v (max z w)}.map
      (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f'.τ₁ (n + 1))) hxy)

/-- The original mapped H0 cycle is evaluated at the actual group identity. -/
theorem original_mapped_zero_cycle
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}}
    {A : DiscreteContAction (TopModuleCat.{max v (max z w)} ℤ) G}
    {B : DiscreteContAction (TopModuleCat.{max z (max v w)} ℤ) H}
    (φ : H →ₜ* G)
    (f : TopRep.res φ (inhomogeneousOriginalTopRep.{0, v, max z w} G A) ⟶
      inhomogeneousOriginalTopRep.{0, z, max v w} H B)
    (c : ContinuousCohomology.cocycles
      (inhomogeneousOriginalTopRep.{0, v, max z w} G A) 0) :
    ((ContinuousCohomology.zeroIso
      (inhomogeneousOriginalTopRep.{0, z, max v w} H B)).hom
      (nativeGroupCoefficientCohomologyMap.{0, v, z, w} φ f 0
        (ContinuousCohomology.π (inhomogeneousOriginalTopRep.{0, v, max z w} G A) 0 c))).val =
      f.hom (((TopRep.homogeneousCochains
        (inhomogeneousOriginalTopRep.{0, v, max z w} G A)).iCycles 0 c).val 1) := by
  have h := congrArg (fun q =>
    (q (ContinuousCohomology.π (inhomogeneousOriginalTopRep.{0, v, max z w} G A) 0 c)).val)
    (nativeGroupCoefficientZeroIso_naturality.{0, v, z, w} φ f)
  exact h.trans (congrArg f.hom
    (homogeneousZeroIso_cycles_value.{0, v, max z w}
      (inhomogeneousOriginalTopRep.{0, v, max z w} G A) c))

end ContinuousCohomology.Tests

end
