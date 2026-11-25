/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientCupProduct
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientLongExact

/-! # Original native tensor cups under genuine group and coefficient restriction -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v w r
open CategoryTheory

open scoped TensorProduct

namespace ContinuousCohomology

variable {R : Type u} [CommRing R] [TopologicalSpace R]
variable {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{w}}
variable {A B : TopRep.{max v (max w r), u, v} R G}
variable {A' B' : TopRep.{max w (max v r), u, w} R H}
variable [DiscreteTopology A] [DiscreteTopology B]
variable [DiscreteTopology A'] [DiscreteTopology B']

/-- The genuine binary tensor map under an actual group restriction, on original stored modules. -/
def discreteTensorGroupCoefficientHom (φ : H →ₜ* G)
    (f : TopRep.res φ.toMonoidHom A ⟶ A') (g : TopRep.res φ.toMonoidHom B ⟶ B') :
    TopRep.res φ.toMonoidHom (discreteTensorCoefficient.{u, v, max w r} A B) ⟶
        discreteTensorCoefficient.{u, w, max v r} A' B' := by
  letI : DiscreteTopology (TopRep.res φ.toMonoidHom A) := ‹DiscreteTopology A›
  letI : DiscreteTopology (TopRep.res φ.toMonoidHom B) := ‹DiscreteTopology B›
  exact discreteTensorCoefficientMap.{u, w, max v r} f g

/-- The same genuine restricted tensor map has its original factorwise pure tensor value. -/
theorem discreteTensorGroupCoefficientHom_tmul (φ : H →ₜ* G)
    (f : TopRep.res φ.toMonoidHom A ⟶ A') (g : TopRep.res φ.toMonoidHom B ⟶ B') (a : A) (b : B) :
    (discreteTensorGroupCoefficientHom.{u, v, w, r} φ f g).hom (a ⊗ₜ[R] b) =
      f.hom a ⊗ₜ[R] g.hom b := by
  change TensorProduct.map f.hom.toLinearMap g.hom.toLinearMap (a ⊗ₜ[R] b) = _
  exact TensorProduct.map_tmul _ _ _ _

/-- Literal homogeneous tensor cup commutes with every actual group and coefficient map. -/
theorem flatHomogeneousCup_group_naturality (φ : H →ₜ* G)
    (f : TopRep.res φ.toMonoidHom A ⟶ A') (g : TopRep.res φ.toMonoidHom B ⟶ B')
    (p q : ℕ) (x : flatHomogeneousCochains.{u, v, max w r} A p)
        (y : flatHomogeneousCochains.{u, v, max w r} B q) :
    nativeFlatGroupCoefficientTerm.{u, v, w, r} φ
        (discreteTensorGroupCoefficientHom.{u, v, w, r} φ f g) (p + q)
        (flatHomogeneousCup.{u, v, max w r} A B p q x y) =
      flatHomogeneousCup.{u, w, max v r} A' B' p q
        (nativeFlatGroupCoefficientTerm.{u, v, w, r} φ f p x)
        (nativeFlatGroupCoefficientTerm.{u, v, w, r} φ g q y) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rw [nativeFlatGroupCoefficientTerm_apply, flatHomogeneousCup_apply,
    discreteTensorGroupCoefficientHom_tmul, flatHomogeneousCup_apply,
    nativeFlatGroupCoefficientTerm_apply, nativeFlatGroupCoefficientTerm_apply]
  rfl

omit [DiscreteTopology A] [DiscreteTopology A'] in
private theorem nativeGroupCycles_tuple_value (φ : H →ₜ* G)
    (f : TopRep.res φ.toMonoidHom A ⟶ A') (n : ℕ)
    (x : cocycles.{u, v, max w r} A n) (t : Fin (n + 1) → H) :
    resolutionFinUncurry.{u, w, max v r} A' (n + 1)
      (((TopRep.homogeneousCochains.{u, w, max v r} A').iCycles n
        (HomologicalComplex.cyclesMap (nativeGroupCoefficientCochainsMap.{u, v, w, r} φ f) n
            x)).val) t =
      f.hom (resolutionFinUncurry.{u, v, max w r} A (n + 1)
        (((TopRep.homogeneousCochains.{u, v, max w r} A).iCycles n x).val) (fun i => φ (t i))) := by
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (nativeGroupCoefficientCochainsMap.{u, v, w, r} φ f) n) x
  have hv := congrArg (fun c : (TopRep.homogeneousCochains.{u, w, max v r} A').X n =>
    (homogeneousFinContinuousLinearEquiv.{u, w, max v r} A' n c).val t) hi
  exact (homogeneousFinContinuousLinearEquiv_apply.{u, w, max v r} A' n _ t).symm.trans
    (hv.trans ((nativeGroupCoefficientCochainsMap_apply.{u, v, w, r} φ f n _ t).trans
      (congrArg f.hom (homogeneousFinContinuousLinearEquiv_apply.{u, v, max w r} A n _ _))))

private theorem nativeCycleTuple_ext
    {Q : ProfiniteGrp.{v}} (X : TopRep.{max v r, u, v} R Q) (n : ℕ)
    (x y : cocycles.{u, v, r} X n)
    (hv : ∀ t : Fin (n + 1) → Q,
      resolutionFinUncurry.{u, v, r} X (n + 1)
        (((TopRep.homogeneousCochains.{u, v, r} X).iCycles n x).val) t =
      resolutionFinUncurry.{u, v, r} X (n + 1)
        (((TopRep.homogeneousCochains.{u, v, r} X).iCycles n y).val) t) : x = y := by
  apply (ModuleCat.mono_iff_injective (homogeneousNativeModuleCyclesIso.{u, v, r} X n).hom).mp
      inferInstance
  apply (ModuleCat.mono_iff_injective ((flatHomogeneousModuleComplex.{u, v, r} X).iCycles n)).mp
      inferInstance
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact (homogeneousNativeModuleCyclesIso_tuple_value.{u, v, r} X n x t).trans
    ((hv t).trans (homogeneousNativeModuleCyclesIso_tuple_value.{u, v, r} X n y t).symm)

/-- Every original native cycle cup commutes with the actual group/coefficient map. -/
theorem discreteContinuousCupCocycles_group_naturality (φ : H →ₜ* G)
    (f : TopRep.res φ.toMonoidHom A ⟶ A') (g : TopRep.res φ.toMonoidHom B ⟶ B')
    (p q : ℕ) (x : cocycles.{u, v, max w r} A p) (y : cocycles.{u, v, max w r} B q) :
    HomologicalComplex.cyclesMap (nativeGroupCoefficientCochainsMap.{u, v, w, r} φ
      (discreteTensorGroupCoefficientHom.{u, v, w, r} φ f g)) (p + q)
      (discreteContinuousCupCocycles.{u, v, max w r} A B p q x y) =
    discreteContinuousCupCocycles.{u, w, max v r} A' B' p q
      (HomologicalComplex.cyclesMap (nativeGroupCoefficientCochainsMap.{u, v, w, r} φ f) p x)
      (HomologicalComplex.cyclesMap (nativeGroupCoefficientCochainsMap.{u, v, w, r} φ g) q y) := by
  apply nativeCycleTuple_ext.{u, w, max v r}
    (discreteTensorCoefficient.{u, w, max v r} A' B') (p + q)
  intro t
  have h₁ := nativeGroupCycles_tuple_value.{u, v, w, r} φ
    (discreteTensorGroupCoefficientHom.{u, v, w, r} φ f g) (p + q)
    (discreteContinuousCupCocycles.{u, v, max w r} A B p q x y) t
  have h₂ := congrArg (discreteTensorGroupCoefficientHom.{u, v, w, r} φ f g).hom
    (discreteContinuousCupCocycles_tuple_value.{u, v, max w r} A B p q x y (fun i => φ (t i)))
  have h₃ := discreteTensorGroupCoefficientHom_tmul.{u, v, w, r} φ f g
    (resolutionFinUncurry.{u, v, max w r} A (p + 1)
      (((TopRep.homogeneousCochains.{u, v, max w r} A).iCycles p x).val)
      (homogeneousCupFront p q (fun i => φ (t i))))
    (resolutionFinUncurry.{u, v, max w r} B (q + 1)
      (((TopRep.homogeneousCochains.{u, v, max w r} B).iCycles q y).val)
      (homogeneousCupBack p q (fun i => φ (t i))))
  have h₄ := congrArg₂ (fun a b => a ⊗ₜ[R] b)
    (nativeGroupCycles_tuple_value.{u, v, w, r} φ f p x (homogeneousCupFront p q t)).symm
    (nativeGroupCycles_tuple_value.{u, v, w, r} φ g q y (homogeneousCupBack p q t)).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans
    (discreteContinuousCupCocycles_tuple_value.{u, w, max v r} A' B' p q _ _ t).symm)))

private theorem originalPi_surjective
    {Q : ProfiniteGrp.{v}} (X : TopRep.{max v r, u, v} R Q) (n : ℕ) :
    Function.Surjective (π.{u, v, r} X n) := by
  exact (ModuleCat.epi_iff_surjective
    ((forget₂ (TopModuleCat.{max v r} R) (ModuleCat.{max v r} R)).map (π.{u, v, r} X n))).mp
        inferInstance

omit [DiscreteTopology A] [DiscreteTopology A'] in
private theorem nativeGroupH_pi (φ : H →ₜ* G)
    (f : TopRep.res φ.toMonoidHom A ⟶ A') (n : ℕ) (x : cocycles.{u, v, max w r} A n) :
    nativeGroupCoefficientCohomologyMap.{u, v, w, r} φ f n (π.{u, v, max w r} A n x) =
      π.{u, w, max v r} A' n
        (HomologicalComplex.cyclesMap (nativeGroupCoefficientCochainsMap.{u, v, w, r} φ f) n x) :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality
        (nativeGroupCoefficientCochainsMap.{u, v, w, r} φ f) n) x

/-- Original native continuous cup is multiplicative under every actual group/coefficient map,
with independent source and target group universes and all original cohomology degrees. -/
theorem discreteContinuousCup_group_naturality (φ : H →ₜ* G)
    (f : TopRep.res φ.toMonoidHom A ⟶ A') (g : TopRep.res φ.toMonoidHom B ⟶ B')
    (p q : ℕ) (a : continuousCohomology.{u, v, max w r} p A)
    (b : continuousCohomology.{u, v, max w r} q B) :
    nativeGroupCoefficientCohomologyMap.{u, v, w, r} φ
        (discreteTensorGroupCoefficientHom.{u, v, w, r} φ f g) (p + q)
        (discreteContinuousCup.{u, v, max w r} A B p q a b) =
      discreteContinuousCup.{u, w, max v r} A' B' p q
        (nativeGroupCoefficientCohomologyMap.{u, v, w, r} φ f p a)
        (nativeGroupCoefficientCohomologyMap.{u, v, w, r} φ g q b) := by
  obtain ⟨x, rfl⟩ := originalPi_surjective.{u, v, max w r} A p a
  obtain ⟨y, rfl⟩ := originalPi_surjective.{u, v, max w r} B q b
  calc
    _ = nativeGroupCoefficientCohomologyMap.{u, v, w, r} φ
        (discreteTensorGroupCoefficientHom.{u, v, w, r} φ f g) (p + q)
        (π.{u, v, max w r} (discreteTensorCoefficient.{u, v, max w r} A B) (p + q)
          (discreteContinuousCupCocycles.{u, v, max w r} A B p q x y)) :=
      congrArg (nativeGroupCoefficientCohomologyMap.{u, v, w, r} φ
        (discreteTensorGroupCoefficientHom.{u, v, w, r} φ f g) (p + q))
        (discreteContinuousCup_pi.{u, v, max w r} A B p q x y)
    _ = π.{u, w, max v r} (discreteTensorCoefficient.{u, w, max v r} A' B') (p + q)
        (HomologicalComplex.cyclesMap (nativeGroupCoefficientCochainsMap.{u, v, w, r} φ
          (discreteTensorGroupCoefficientHom.{u, v, w, r} φ f g)) (p + q)
          (discreteContinuousCupCocycles.{u, v, max w r} A B p q x y)) :=
      nativeGroupH_pi.{u, v, w, r} φ
          (discreteTensorGroupCoefficientHom.{u, v, w, r} φ f g) (p + q) _
    _ = π.{u, w, max v r} (discreteTensorCoefficient.{u, w, max v r} A' B') (p + q)
        (discreteContinuousCupCocycles.{u, w, max v r} A' B' p q
          (HomologicalComplex.cyclesMap (nativeGroupCoefficientCochainsMap.{u, v, w, r} φ f) p x)
          (HomologicalComplex.cyclesMap
              (nativeGroupCoefficientCochainsMap.{u, v, w, r} φ g) q y)) :=
      congrArg (π.{u, w, max v r} (discreteTensorCoefficient.{u, w, max v r} A' B') (p + q))
        (discreteContinuousCupCocycles_group_naturality.{u, v, w, r} φ f g p q x y)
    _ = discreteContinuousCup.{u, w, max v r} A' B' p q
        (π.{u, w, max v r} A' p
          (HomologicalComplex.cyclesMap (nativeGroupCoefficientCochainsMap.{u, v, w, r} φ f) p x))
        (π.{u, w, max v r} B' q
          (HomologicalComplex.cyclesMap
              (nativeGroupCoefficientCochainsMap.{u, v, w, r} φ g) q y)) :=
      (discreteContinuousCup_pi.{u, w, max v r} A' B' p q _ _).symm
    _ = _ := congrArg₂ (fun a b => discreteContinuousCup.{u, w, max v r} A' B' p q a b)
      (nativeGroupH_pi.{u, v, w, r} φ f p x).symm (nativeGroupH_pi.{u, v, w, r} φ g q y).symm


private theorem originalGroupCycles_tuple_value
    {G₀ H₀ : ProfiniteGrp.{v}}
    {X : TopRep.{max v r, u, v} R G₀} {X' : TopRep.{max v r, u, v} R H₀}
    (φ : H₀ →ₜ* G₀) (f : TopRep.res φ.toMonoidHom X ⟶ X') (n : ℕ)
    (x : cocycles.{u, v, r} X n) (t : Fin (n + 1) → H₀) :
    resolutionFinUncurry.{u, v, r} X' (n + 1)
      (((TopRep.homogeneousCochains.{u, v, r} X').iCycles n
        (cocyclesMap φ f n x)).val) t =
      f.hom (resolutionFinUncurry.{u, v, r} X (n + 1)
        (((TopRep.homogeneousCochains.{u, v, r} X).iCycles n x).val) (fun i => φ (t i))) := by
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (show TopRep.homogeneousCochains.{u, v, r} X ⟶
      TopRep.homogeneousCochains.{u, v, r} X' from cochainsMap φ f) n) x
  exact (congrArg (fun c : (TopRep.homogeneousCochains.{u, v, r} X').X n =>
      resolutionFinUncurry.{u, v, r} X' (n + 1) c.val t) hi).trans
    (resolutionFinUncurry_resolutionMap.{u, v, r} φ f (n + 1)
      (((TopRep.homogeneousCochains.{u, v, r} X).iCycles n x).val) t)

/-- The genuine restricted cup cycle square on the same original stock rank. -/
theorem discreteContinuousCupCocycles_group_naturality_original_rank
    {G₀ H₀ : ProfiniteGrp.{v}}
    {X Y : TopRep.{max v r, u, v} R G₀} {X' Y' : TopRep.{max v r, u, v} R H₀}
    [DiscreteTopology X] [DiscreteTopology Y] [DiscreteTopology X'] [DiscreteTopology Y']
    (φ : H₀ →ₜ* G₀) (f : TopRep.res φ.toMonoidHom X ⟶ X') (g : TopRep.res φ.toMonoidHom Y ⟶ Y')
    (p q : ℕ) (x : cocycles.{u, v, r} X p) (y : cocycles.{u, v, r} Y q) :
    cocyclesMap φ (discreteTensorGroupCoefficientHom.{u, v, v, r} φ f g) (p + q)
      (discreteContinuousCupCocycles.{u, v, r} X Y p q x y) =
      discreteContinuousCupCocycles.{u, v, r} X' Y' p q
        (cocyclesMap φ f p x) (cocyclesMap φ g q y) := by
  apply nativeCycleTuple_ext.{u, v, r} (discreteTensorCoefficient.{u, v, r} X' Y') (p + q)
  intro t
  have h₁ := originalGroupCycles_tuple_value.{u, v, r} φ
    (discreteTensorGroupCoefficientHom.{u, v, v, r} φ f g) (p + q)
    (discreteContinuousCupCocycles.{u, v, r} X Y p q x y) t
  have h₂ := congrArg (discreteTensorGroupCoefficientHom.{u, v, v, r} φ f g).hom
    (discreteContinuousCupCocycles_tuple_value.{u, v, r} X Y p q x y (fun i => φ (t i)))
  have h₃ := discreteTensorGroupCoefficientHom_tmul.{u, v, v, r} φ f g
    (resolutionFinUncurry.{u, v, r} X (p + 1)
      (((TopRep.homogeneousCochains.{u, v, r} X).iCycles p x).val)
      (homogeneousCupFront p q (fun i => φ (t i))))
    (resolutionFinUncurry.{u, v, r} Y (q + 1)
      (((TopRep.homogeneousCochains.{u, v, r} Y).iCycles q y).val)
      (homogeneousCupBack p q (fun i => φ (t i))))
  have h₄ := congrArg₂ (fun a b => a ⊗ₜ[R] b)
    (originalGroupCycles_tuple_value.{u, v, r} φ f p x (homogeneousCupFront p q t)).symm
    (originalGroupCycles_tuple_value.{u, v, r} φ g q y (homogeneousCupBack p q t)).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans
    (discreteContinuousCupCocycles_tuple_value.{u, v, r} X' Y' p q _ _ t).symm)))

/-- The same actual group cup square on the original stock rank, for source and target
profinite groups in their given shared universe. -/
theorem discreteContinuousCup_group_naturality_original_rank
    {G₀ H₀ : ProfiniteGrp.{v}}
    {X Y : TopRep.{max v r, u, v} R G₀} {X' Y' : TopRep.{max v r, u, v} R H₀}
    [DiscreteTopology X] [DiscreteTopology Y] [DiscreteTopology X'] [DiscreteTopology Y']
    (φ : H₀ →ₜ* G₀) (f : TopRep.res φ.toMonoidHom X ⟶ X') (g : TopRep.res φ.toMonoidHom Y ⟶ Y')
    (p q : ℕ) (a : continuousCohomology.{u, v, r} p X) (b : continuousCohomology.{u, v, r} q Y) :
    ContinuousCohomology.map φ (discreteTensorGroupCoefficientHom.{u, v, v, r} φ f g) (p + q)
        (discreteContinuousCup.{u, v, r} X Y p q a b) =
      discreteContinuousCup.{u, v, r} X' Y' p q
        (ContinuousCohomology.map φ f p a) (ContinuousCohomology.map φ g q b) := by
  obtain ⟨x, rfl⟩ := originalPi_surjective.{u, v, r} X p a
  obtain ⟨y, rfl⟩ := originalPi_surjective.{u, v, r} Y q b
  rw [discreteContinuousCup_pi.{u, v, r} X Y p q x y]
  have h₁ := ConcreteCategory.congr_hom
    (π_map φ (discreteTensorGroupCoefficientHom.{u, v, v, r} φ f g) (p + q))
    (discreteContinuousCupCocycles.{u, v, r} X Y p q x y)
  have h₂ := congrArg (π.{u, v, r} (discreteTensorCoefficient.{u, v, r} X' Y') (p + q))
    (discreteContinuousCupCocycles_group_naturality_original_rank.{u, v, r} φ f g p q x y)
  have h₃ := (discreteContinuousCup_pi.{u, v, r} X' Y' p q
    (cocyclesMap φ f p x) (cocyclesMap φ g q y)).symm
  have hx := ConcreteCategory.congr_hom (π_map φ f p) x
  have hy := ConcreteCategory.congr_hom (π_map φ g q) y
  exact h₁.trans (h₂.trans (h₃.trans
    (congrArg₂ (fun a b => discreteContinuousCup.{u, v, r} X' Y' p q a b) hx.symm hy.symm)))

end ContinuousCohomology
