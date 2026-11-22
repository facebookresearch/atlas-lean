/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHGenerators
public import MathlibExt.Topology.Category.CGWH.CartesianClosed
public import Mathlib.Topology.Homotopy.TopCat.Basic
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornHomotopy

/-!
# The actual native realized-horn interval action

The finite realized horn retraction and its full relative homotopy are the
original simplicial realization maps. The native Cartesian interval action
uses the actual selected projections and retains both endpoint and fixed-horn
equations.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CGWH

/-- The native horn retraction is the fully faithful preimage of the original
continuous realized-horn retraction on its literal finite carrier. -/
noncomputable def realizedHornRetraction (n : ℕ) (i : Fin (n + 2)) :
    SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}) ⟶
      SSet.toCGWHOfFinite (SSet.horn.{v} (n + 1) i) :=
  fullyFaithfulCgwhToTop.preimage
    (TopCat.ofHom (SSet.realizedHornRetract (n + 1) i (Nat.succ_pos n)))

/-- The native retraction has exactly the original continuous map after forgetting. -/
theorem cgwhToTop_map_realizedHornRetraction (n : ℕ) (i : Fin (n + 2)) :
    cgwhToTop.{u, v}.map (realizedHornRetraction n i) =
      TopCat.ofHom (SSet.realizedHornRetract (n + 1) i (Nat.succ_pos n)) :=
  fullyFaithfulCgwhToTop.map_preimage _

/-- The original pointwise horn retraction gives the entire native inverse equation. -/
theorem realizedHornInclusion_ret (n : ℕ) (i : Fin (n + 2)) :
    realizedHornInclusion.{v, u} n i ≫ realizedHornRetraction n i = 𝟙 _ := by
  have hIncl : cgwhToTop.{u, v}.map (realizedHornInclusion.{v, u} n i) =
      SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι := by
    have hMapped := congrArg
      (fun f : SSet.toCompactlyGeneratedOfFinite (SSet.horn.{v} (n + 1) i) ⟶
          SSet.toCompactlyGeneratedOfFinite (Δ[n + 1] : SSet.{v}) =>
        CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map f)
      (cgwhToCompactlyGenerated_map_realizedHornInclusion.{u, v} n i)
    exact hMapped.trans
      (CompactlyGenerated.compactlyGeneratedToTop_map_realizedHornInclusion.{u, v} n i)
  apply cgwhToTop.map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, hIncl,
    cgwhToTop_map_realizedHornRetraction]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact SSet.realizedHornRetract_ι (n + 1) i (Nat.succ_pos n) x

/-- The original full realized-horn homotopy is retained on the native carrier,
with its actual mapped identity and retraction-composite endpoints. -/
noncomputable def realizedHornRetractionHomotopy (n : ℕ) (i : Fin (n + 2)) :
    TopCat.Homotopy
      (cgwhToTop.{u, v}.map
        (𝟙 (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}))))
      (cgwhToTop.{u, v}.map
        (realizedHornRetraction n i ≫ realizedHornInclusion.{v, u} n i)) := by
  have hIncl : cgwhToTop.{u, v}.map (realizedHornInclusion.{v, u} n i) =
      SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι := by
    have hMapped := congrArg
      (fun f : SSet.toCompactlyGeneratedOfFinite (SSet.horn.{v} (n + 1) i) ⟶
          SSet.toCompactlyGeneratedOfFinite (Δ[n + 1] : SSet.{v}) =>
        CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map f)
      (cgwhToCompactlyGenerated_map_realizedHornInclusion.{u, v} n i)
    exact hMapped.trans
      (CompactlyGenerated.compactlyGeneratedToTop_map_realizedHornInclusion.{u, v} n i)
  have hId : (cgwhToTop.{u, v}.map
      (𝟙 (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v})))).hom =
        ContinuousMap.id _ := by
    exact congrArg TopCat.Hom.hom (CategoryTheory.Functor.map_id cgwhToTop _)
  have hComp :
      (cgwhToTop.{u, v}.map
        (realizedHornRetraction n i ≫ realizedHornInclusion.{v, u} n i)).hom =
        ((SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι).hom).comp
          (SSet.realizedHornRetract (n + 1) i (Nat.succ_pos n)) := by
    rw [CategoryTheory.Functor.map_comp, cgwhToTop_map_realizedHornRetraction, hIncl]
    rfl
  exact ContinuousMap.Homotopy.cast
    (SSet.realizedHornHomotopy (n + 1) i (Nat.succ_pos n)) hId.symm hComp.symm

/-- The transported full homotopy fixes every actual included horn point. -/
theorem realizedHornRetractionHomotopy_fix (n : ℕ) (i : Fin (n + 2))
    (t : unitInterval)
    (x : (SSet.toCGWHOfFinite (SSet.horn.{v} (n + 1) i) : CGWH.{u, v})) :
    realizedHornRetractionHomotopy.{u, v} n i
      (t, realizedHornInclusion.{v, u} n i x) =
        realizedHornInclusion.{v, u} n i x := by
  have hIncl : cgwhToTop.{u, v}.map (realizedHornInclusion.{v, u} n i) =
      SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι := by
    have hMapped := congrArg
      (fun f : SSet.toCompactlyGeneratedOfFinite (SSet.horn.{v} (n + 1) i) ⟶
          SSet.toCompactlyGeneratedOfFinite (Δ[n + 1] : SSet.{v}) =>
        CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map f)
      (cgwhToCompactlyGenerated_map_realizedHornInclusion.{u, v} n i)
    exact hMapped.trans
      (CompactlyGenerated.compactlyGeneratedToTop_map_realizedHornInclusion.{u, v} n i)
  have hx : realizedHornInclusion.{v, u} n i x =
      SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι x :=
    ConcreteCategory.congr_hom hIncl x
  have hInput :
      (SSet.realizedHornHomotopy (n + 1) i (Nat.succ_pos n))
        (t, realizedHornInclusion.{v, u} n i x) =
      (SSet.realizedHornHomotopy (n + 1) i (Nat.succ_pos n))
        (t, SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι x) :=
    congrArg
      (fun y : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) =>
        (SSet.realizedHornHomotopy (n + 1) i (Nat.succ_pos n)) (t, y)) hx
  have hOriginal :
      (SSet.realizedHornHomotopy (n + 1) i (Nat.succ_pos n))
        (t, SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι x) =
      SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι x :=
    SSet.realizedHornHomotopyMap_fix (n + 1) i (Nat.succ_pos n) x t
  exact hInput.trans (hOriginal.trans hx.symm)

/-- The literal compact interval, lifted to the native carrier universe. -/
noncomputable def homotopyInterval : CGWH.{u, v} :=
  CGWH.of (ULift.{v, 0} unitInterval)

/-- A time parameter determines an actual map from the selected tensor unit. -/
noncomputable def homotopyIntervalEndpoint (t : unitInterval) :
    𝟙_ CGWH.{u, v} ⟶ homotopyInterval.{u, v} :=
  ConcreteCategory.ofHom (ContinuousMap.const _ (ULift.up t))

/-- The original jointly continuous homotopy is a native interval-first map,
computed through the two selected Cartesian projections. -/
noncomputable def intervalHomotopyTensor {A : CGWH.{u, v}}
    (f₀ f₁ : A ⟶ A)
    (H : TopCat.Homotopy (cgwhToTop.map f₀) (cgwhToTop.map f₁)) :
    homotopyInterval.{u, v} ⊗ A ⟶ A :=
  ConcreteCategory.ofHom
    ⟨fun z => H ((CartesianMonoidalCategory.fst
        homotopyInterval A z).down,
        CartesianMonoidalCategory.snd homotopyInterval A z),
      H.toContinuousMap.continuous.comp
        ((continuous_uliftDown.comp
          (ConcreteCategory.hom (CartesianMonoidalCategory.fst
            homotopyInterval A)).continuous).prodMk
          (ConcreteCategory.hom (CartesianMonoidalCategory.snd
            homotopyInterval A)).continuous)⟩

/-- Evaluation of the whole selected tensor map is the original homotopy. -/
theorem intervalHomotopyTensor_apply {A : CGWH.{u, v}}
    (f₀ f₁ : A ⟶ A)
    (H : TopCat.Homotopy (cgwhToTop.map f₀) (cgwhToTop.map f₁))
    (z : (homotopyInterval.{u, v} ⊗ A : CGWH.{u, v})) :
    intervalHomotopyTensor f₀ f₁ H z =
      H ((CartesianMonoidalCategory.fst homotopyInterval A z).down,
        CartesianMonoidalCategory.snd homotopyInterval A z) :=
  rfl

/-- A pointwise endpoint of the original homotopy supplies the complete
unitor-and-tensor endpoint equation on the native selected product. -/
theorem intervalHomotopyTensor_endpoint {A : CGWH.{u, v}}
    (f₀ f₁ : A ⟶ A)
    (H : TopCat.Homotopy (cgwhToTop.map f₀) (cgwhToTop.map f₁))
    (t : unitInterval) (f : A ⟶ A)
    (ht : ∀ a : A, H (t, a) = f a) :
    (λ_ A).inv ≫ (homotopyIntervalEndpoint t ⊗ₘ 𝟙 A) ≫
        intervalHomotopyTensor f₀ f₁ H = f := by
  let j : A ⟶ homotopyInterval.{u, v} ⊗ A :=
    (λ_ A).inv ≫ (homotopyIntervalEndpoint t ⊗ₘ 𝟙 A)
  have hFirst : j ≫ CartesianMonoidalCategory.fst homotopyInterval A =
      CartesianMonoidalCategory.toUnit A ≫ homotopyIntervalEndpoint t := by
    dsimp only [j]
    simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst]
    have hUnit : (λ_ A).inv ≫
        CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, v}) A =
          CartesianMonoidalCategory.toUnit A :=
      CartesianMonoidalCategory.toUnit_unique _ _
    simpa only [Category.assoc] using congrArg
      (fun f : A ⟶ 𝟙_ CGWH.{u, v} => f ≫ homotopyIntervalEndpoint t) hUnit
  have hSecond : j ≫ CartesianMonoidalCategory.snd homotopyInterval A =
      𝟙 A := by
    dsimp only [j]
    simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
      CartesianMonoidalCategory.leftUnitor_inv_snd, Category.comp_id]
  change j ≫ intervalHomotopyTensor f₀ f₁ H = f
  apply ConcreteCategory.hom_ext
  intro a
  have hTime : (CartesianMonoidalCategory.fst homotopyInterval A (j a)).down =
      t := by
    have h := ConcreteCategory.congr_hom hFirst a
    change (CartesianMonoidalCategory.fst homotopyInterval A) (j a) =
      homotopyIntervalEndpoint t (CartesianMonoidalCategory.toUnit A a) at h
    rw [h]
    rfl
  have hSpace : CartesianMonoidalCategory.snd homotopyInterval A (j a) = a := by
    exact ConcreteCategory.congr_hom hSecond a
  change intervalHomotopyTensor f₀ f₁ H (j a) = f a
  rw [intervalHomotopyTensor_apply, hTime, hSpace]
  exact ht a

/-- The original pointwise fixed-subspace condition gives the complete
categorical relative equation, using the actual terminal collapse map. -/
theorem intervalHomotopyTensor_fix {X A : CGWH.{u, v}}
    (f₀ f₁ : A ⟶ A)
    (H : TopCat.Homotopy (cgwhToTop.map f₀) (cgwhToTop.map f₁))
    (i : X ⟶ A) (hfix : ∀ (t : unitInterval) (x : X), H (t, i x) = i x) :
    (𝟙 homotopyInterval ⊗ₘ i) ≫ intervalHomotopyTensor f₀ f₁ H =
      (CartesianMonoidalCategory.toUnit homotopyInterval ⊗ₘ 𝟙 X) ≫
        (λ_ X).hom ≫ i := by
  have hProjection :
      (CartesianMonoidalCategory.toUnit homotopyInterval ⊗ₘ 𝟙 X) ≫
        (λ_ X).hom = CartesianMonoidalCategory.snd homotopyInterval X := by
    simpa only [tensorHom_id] using
      (CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_hom
        homotopyInterval X)
  rw [← Category.assoc, hProjection]
  apply ConcreteCategory.hom_ext
  intro z
  have hFirst : CartesianMonoidalCategory.fst homotopyInterval A
      ((𝟙 homotopyInterval ⊗ₘ i) z) =
        CartesianMonoidalCategory.fst homotopyInterval X z := by
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_fst (𝟙 homotopyInterval) i) z
  have hSecond : CartesianMonoidalCategory.snd homotopyInterval A
      ((𝟙 homotopyInterval ⊗ₘ i) z) =
        i (CartesianMonoidalCategory.snd homotopyInterval X z) := by
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_snd (𝟙 homotopyInterval) i) z
  change intervalHomotopyTensor f₀ f₁ H ((𝟙 homotopyInterval ⊗ₘ i) z) =
    i (CartesianMonoidalCategory.snd homotopyInterval X z)
  rw [intervalHomotopyTensor_apply, hFirst, hSecond]
  exact hfix _ _

/-- The native horn interval action retains the entire original geometric
homotopy, retraction and inclusion. -/
noncomputable def realizedHornIntervalAction (n : ℕ) (i : Fin (n + 2)) :
    homotopyInterval.{u, v} ⊗ SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}) ⟶
      SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}) :=
  intervalHomotopyTensor (𝟙 _)
    (realizedHornRetraction n i ≫ realizedHornInclusion n i)
    (realizedHornRetractionHomotopy.{u, v} n i)

/-- At zero, the actual whole native horn action is the identity. -/
theorem realizedHornIntervalAction_zero (n : ℕ) (i : Fin (n + 2)) :
    (λ_ (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}))).inv ≫
        (homotopyIntervalEndpoint.{u, v} 0 ⊗ₘ 𝟙 _) ≫
        realizedHornIntervalAction n i = 𝟙 _ := by
  apply intervalHomotopyTensor_endpoint
  intro x
  exact (realizedHornRetractionHomotopy.{u, v} n i).apply_zero x

/-- At one, the actual whole native action is inclusion after the original retraction. -/
theorem realizedHornIntervalAction_one (n : ℕ) (i : Fin (n + 2)) :
    (λ_ (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}))).inv ≫
        (homotopyIntervalEndpoint.{u, v} 1 ⊗ₘ 𝟙 _) ≫
        realizedHornIntervalAction n i =
      realizedHornRetraction n i ≫ realizedHornInclusion n i := by
  apply intervalHomotopyTensor_endpoint
  intro x
  exact (realizedHornRetractionHomotopy.{u, v} n i).apply_one x

/-- The full actual horn action fixes the original included horn throughout
its native interval, not only at the two endpoints. -/
theorem realizedHornIntervalAction_fix (n : ℕ) (i : Fin (n + 2)) :
    (𝟙 homotopyInterval ⊗ₘ realizedHornInclusion.{v, u} n i) ≫
        realizedHornIntervalAction n i =
      (CartesianMonoidalCategory.toUnit homotopyInterval ⊗ₘ 𝟙 _) ≫
        (λ_ (SSet.toCGWHOfFinite (SSet.horn.{v} (n + 1) i))).hom ≫
        realizedHornInclusion n i := by
  apply intervalHomotopyTensor_fix
  exact realizedHornRetractionHomotopy_fix.{u, v} n i

end CGWH
