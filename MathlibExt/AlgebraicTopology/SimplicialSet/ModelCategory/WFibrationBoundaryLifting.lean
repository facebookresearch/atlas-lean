/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetSquareTransport
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WFibrationFiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanSphereFiller

/-!
# Boundary lifting for weak-equivalence Kan fibrations

Let `X` and `Y` be Kan complexes, and let `f : X → Y` be both a Kan fibration
and a Kan-complex weak equivalence. For every dimension `n` and every fixed top
map `∂Δ[n] → X`, each commuting boundary square over `f` has a diagonal lift.

The boundary inclusion is the left map and `f` is the right map. The result uses
nonempty strict fibers with trivial pointed homotopy groups, together with boundary
sphere filling in the Kan fibers. See Goerss–Jardine, Simplicial Homotopy Theory,
Chapter I.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet

/--
For a Kan fibration `f : X → Y` between Kan complexes that is a Kan-complex weak
equivalence, every commuting square with left map `∂Δ[n] → Δ[n]` and a fixed
top map `∂Δ[n] → X` admits a diagonal lift, for every `n`.
-/
theorem KanComplex.W.hasLiftingPropertyFixedTop
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f : X ⟶ Y} [Fibration f] (hf : KanComplex.W f) {n : ℕ}
    (top : (SSet.boundary n : SSet.{u}) ⟶ X) :
    HasLiftingPropertyFixedTop (SSet.boundary n).ι f top := by
  intro b sq₀
  obtain ⟨y, t₁, sq₁, ht₁f, hiff⟩ :=
    CommSq.exists_const_base_reduction sq₀
  obtain ⟨x, hx⟩ := KanComplex.W.exists_vertex_over hf y
  have hπ : ∀ (m : ℕ) (z : (Subcomplex.fiber f y : SSet.{u}) _⦋0⦌),
      Subsingleton (KanComplex.π m (Subcomplex.fiber f y : SSet.{u}) z) :=
    fun m z => subsingleton_π_fiber_of_W_fibration hf y m z
  have hle : Subcomplex.range t₁ ≤ Subcomplex.fiber f y :=
    (Subcomplex.range_le_fiber_iff f y t₁).mpr ht₁f
  obtain ⟨d, hd⟩ := KanComplex.exists_boundary_filler_of_subsingleton_pi
    (Subcomplex.fiber.basePoint x hx) hπ (Subcomplex.lift t₁ hle)
  refine hiff.mpr (CommSq.HasLift.mk' ⟨d ≫ (Subcomplex.fiber f y).ι, ?_, ?_⟩)
  · calc (SSet.boundary n).ι ≫ (d ≫ (Subcomplex.fiber f y).ι)
        = ((SSet.boundary n).ι ≫ d) ≫ (Subcomplex.fiber f y).ι := by
          rw [Category.assoc]
      _ = Subcomplex.lift t₁ hle ≫ (Subcomplex.fiber f y).ι := by rw [hd]
      _ = t₁ := Subcomplex.lift_ι t₁ hle
  · calc (d ≫ (Subcomplex.fiber f y).ι) ≫ f
        = d ≫ ((Subcomplex.fiber f y).ι ≫ f) := by rw [← Category.assoc]
      _ = d ≫ SSet.const y := by rw [Subcomplex.fiber_ι_comp]
      _ = SSet.const y := SSet.comp_const d y

end SSet
