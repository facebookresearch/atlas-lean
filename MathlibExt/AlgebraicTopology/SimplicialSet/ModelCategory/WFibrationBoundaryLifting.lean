/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetSquareTransport
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WFibrationFiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanSphereFiller

/-!
# Fixed-top boundary lifting for weak-equivalence Kan fibrations

Let `f : X ⟶ Y` be a Kan fibration between Kan complexes satisfying
`KanComplex.W f`. Every commuting square with a boundary inclusion on the
left admits a lift when its top map is fixed. The proof reduces to a strict
fiber, uses the vanishing of its pointed homotopy groups to fill the boundary
sphere, and transports the lift back to the original square. This is the
fiber sphere-filling argument of Goerss–Jardine, *Simplicial Homotopy Theory*,
Chapter I.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet

/-- For a weak-equivalence Kan fibration between Kan complexes, every
boundary square with a fixed top map admits a lift. The boundary inclusion
is the left map and `f` is the right map. -/
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
