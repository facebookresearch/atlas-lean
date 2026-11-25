/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.BoundaryConeHornIso
public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.TerminalCorner

/-!
# The exact original terminal slice criterion

The original full terminal-boundary condition is equivalent to boundary
lifting for the actual over-slice projection. The reverse direction uses
the canonical cone–horn isomorphism, retaining the entire old boundary
and missing base face. The existing monomorphism lifting-class theorem
then identifies this with lifting against all original monomorphisms.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet.WalkingAdjunction

private theorem terminalSlice_cone_precomp {H A B : SSet.{u}} (t : (Δ[0] : SSet.{u}) ⟶ H)
    (q : B ⟶ sliceOver H t) (i : A ⟶ B) :
    (sliceOver.homEquiv H t A (i ≫ q)).val =
      (join.map i).app Δ[0] ≫ (sliceOver.homEquiv H t B q).val := by
  simp only [sliceOver.homEquiv_apply, Category.assoc,
    CategoryTheory.Functor.map_comp, NatTrans.comp_app]

/-- Actual over-slice boundary lifts derive the intrinsic terminal-boundary condition. -/
theorem rightTerminalVertex_of_slice_boundary {H : SSet.{u}} (t : (Δ[0] : SSet.{u}) ⟶ H)
    (hp : ∀ n : ℕ, HasLiftingProperty (boundary n).ι (sliceOver.proj H t)) : RightTerminalVertex t := by
  intro n b hb
  let q : (∂Δ[n] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H :=
    (BoundaryConeHornIso.fullIso n).hom ≫ BoundaryConeHornIso.hornToBoundary n ≫ b
  have qa : joinInr (∂Δ[n] : SSet.{u}) Δ[0] ≫ q = t := by
    have h := congrArg (fun f => f ≫ b) (BoundaryConeHornIso.fullIso_apex_boundary.{u} n)
    have ha : joinInr (∂Δ[n] : SSet.{u}) Δ[0] ≫ q =
        stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫ boundary.ι (0 : Fin (n + 2)) ≫ b := by
      simpa only [q, Category.assoc] using h
    exact ha.trans hb
  let u₀ : (∂Δ[n] : SSet.{u}) ⟶ sliceOver H t := (sliceOver.homEquiv H t _).symm ⟨q, qa⟩
  have hu : (sliceOver.homEquiv H t _ u₀).val = q :=
    congrArg Subtype.val ((sliceOver.homEquiv H t _).apply_symm_apply ⟨q, qa⟩)
  let base : (Δ[n] : SSet.{u}) ⟶ H := boundary.ι (Fin.last (n + 1)) ≫ b
  have qb : joinInl (∂Δ[n] : SSet.{u}) Δ[0] ≫ q = (boundary n).ι ≫ base := by
    have h := congrArg (fun f => f ≫ b) (BoundaryConeHornIso.fullIso_base_boundary.{u} n)
    simpa only [q, base, Category.assoc] using h
  have hub : u₀ ≫ sliceOver.proj H t = (boundary n).ι ≫ base :=
    (TerminalCorner.cone_base t u₀).symm.trans ((congrArg (fun p => joinInl (∂Δ[n] : SSet.{u}) Δ[0] ≫ p) hu).trans qb)
  let square : CommSq u₀ (boundary n).ι (sliceOver.proj H t) base := ⟨hub⟩
  let _ : HasLiftingProperty (boundary n).ι (sliceOver.proj H t) := hp n
  let whole : (Δ[n] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H :=
    (sliceOver.homEquiv H t Δ[n] square.lift).val
  have hwhole : (join.map (boundary n).ι).app Δ[0] ≫ whole = q := by
    calc
      _ = (sliceOver.homEquiv H t _ ((boundary n).ι ≫ square.lift)).val :=
        (terminalSlice_cone_precomp t square.lift (boundary n).ι).symm
      _ = (sliceOver.homEquiv H t _ u₀).val :=
        congrArg (fun f => (sliceOver.homEquiv H t _ f).val) square.fac_left
      _ = q := hu
  have hbase : joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ whole = base :=
    (TerminalCorner.cone_base t square.lift).trans square.fac_right
  let σ : (Δ[n + 1] : SSet.{u}) ⟶ H := (joinStdSimplexIso n 0).inv ≫ whole
  have hσbase : stdSimplex.δ (Fin.last (n + 1)) ≫ σ = base := by
    dsimp only [σ]
    rw [← Category.assoc, ConeSimplexBoundary.last_face_join_inv]
    exact hbase
  have hσhorn : (horn (n + 1) (Fin.last (n + 1))).ι ≫ σ =
      BoundaryConeHornIso.hornToBoundary n ≫ b := by
    apply (cancel_epi (BoundaryConeHornIso.fullIso.{u} n).hom).mp
    rw [← Category.assoc, BoundaryConeHornIso.fullIso_standard]
    dsimp only [σ]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hwhole
  refine ⟨σ, ?_⟩
  apply boundary.hom_ext
  intro j
  rw [boundary.ι_ι_assoc]
  by_cases hj : j = Fin.last (n + 1)
  · subst j
    exact hσbase
  · calc
      stdSimplex.δ j ≫ σ = horn.ι (Fin.last (n + 1)) j hj ≫
          (horn (n + 1) (Fin.last (n + 1))).ι ≫ σ := (horn.ι_ι_assoc _ _ _ σ).symm
      _ = horn.ι (Fin.last (n + 1)) j hj ≫ BoundaryConeHornIso.hornToBoundary n ≫ b := by rw [hσhorn]
      _ = boundary.ι j ≫ b := by rw [← Category.assoc, BoundaryConeHornIso.hornFace_boundary]

/-- The original terminal-boundary condition is exactly boundary lifting for the actual over-slice. -/
theorem rightTerminalVertex_iff_slice_boundary {H : SSet.{u}} (t : (Δ[0] : SSet.{u}) ⟶ H) :
    RightTerminalVertex t ↔ ∀ n : ℕ, HasLiftingProperty (boundary n).ι (sliceOver.proj H t) :=
  ⟨fun ht n => TerminalCorner.hasLiftingProperty_boundary t ht n,
    rightTerminalVertex_of_slice_boundary t⟩

/-- The original terminal point is exactly a generating-boundary right lift for its actual slice projection. -/
theorem rightTerminalVertex_iff_slice_rlp_I {H : SSet.{u}} (t : (Δ[0] : SSet.{u}) ⟶ H) :
    RightTerminalVertex t ↔ modelCategoryQuillen.I.rlp (sliceOver.proj H t) := by
  rw [rightTerminalVertex_iff_slice_boundary]
  constructor
  · intro hp
    rintro _ _ _ ⟨n⟩
    exact hp n
  · intro hp n
    exact hp _ (modelCategoryQuillen.boundary_ι_mem_I n)

/-- The actual over-slice projection at an intrinsic terminal point lifts every original monomorphism,
and that whole lifting property conversely derives intrinsic terminality. -/
theorem rightTerminalVertex_iff_slice_rlp_mono {H : SSet.{u}} (t : (Δ[0] : SSet.{u}) ⟶ H) :
    RightTerminalVertex t ↔ (MorphismProperty.monomorphisms SSet.{u}).rlp (sliceOver.proj H t) := by
  rw [SSet.rlp_monomorphisms]
  exact rightTerminalVertex_iff_slice_rlp_I t

end SSet.WalkingAdjunction
