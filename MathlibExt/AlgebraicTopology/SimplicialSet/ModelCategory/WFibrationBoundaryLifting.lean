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
# Fixed-top boundary lifting for weak-equivalence fibrations between Kan complexes

Orientation: the boundary inclusion `(SSet.boundary n).ι` is on the left and
the fibration `f : X ⟶ Y` is on the right; the top map `top` is fixed while
the bottom map varies.

Hypotheses: `X` and `Y` are Kan complexes, `f` is a Kan fibration, and
`SSet.KanComplex.W f` holds (all pointed homotopy-group maps are bijective).

Conclusion: every boundary square with the given fixed top admits a lift.

Proof (Goerss--Jardine, *Simplicial Homotopy Theory*, Chapter I, fiber
sphere-filling argument): reduce to constant base via
`SSet.CommSq.exists_const_base_reduction`, pick a vertex over the constant
value via `SSet.KanComplex.W.exists_vertex_over`, note all pointed homotopy
groups of that fibrant strict fiber vanish via
`SSet.subsingleton_π_fiber_of_W_fibration`, fill the induced boundary sphere
in the fiber via `SSet.KanComplex.exists_boundary_filler_of_subsingleton_pi`,
compose with the fiber inclusion, and transport the lift back through the
reduction equivalence.

Explicit nonclaims: no arbitrary `I.rlp`, no `W.mem_rlp_I`, no
model-category instance, no factorization, no filtered-colimit or anodyne
stability, and no result for non-Kan endpoints.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet

/-- Fixed-top boundary lifting for a weak-equivalence fibration between Kan
complexes: with the top map `top` fixed, every boundary square over `f`
admits a lift. The left map is the boundary inclusion `(SSet.boundary n).ι`
and the right map is `f`. This is the Kan-restricted fixed-top half of the
key weak-equivalence-fibration characterization; it claims nothing about
arbitrary `I.rlp`, model structures, or non-Kan endpoints. -/
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
