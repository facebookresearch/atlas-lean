/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Constants
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit

/-!
# Literal marked sections of the parameter product

A chosen original parameter vertex gives the actual section with constant
first coordinate and identity source coordinate. In degree one it sends a
marked source edge to precisely its pair with the degenerate parameter
edge. Restriction from the zero parameter gives this same section.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original marked section at a vertex of the minimally marked parameter. -/
def parameterSection (X : Marked.{u}) {n : ℕ} (v : (Δ[n] : SSet.{u}) _⦋0⦌) :
    X ⟶ prod (min (Δ[n] : SSet.{u})) X :=
  prodLift (const v) (𝟙 X)

/-- The complete original source coordinate is fixed by the generic parameter section. -/
theorem parameterSection_snd (X : Marked.{u}) {n : ℕ}
    (v : (Δ[n] : SSet.{u}) _⦋0⦌) :
    parameterSection X v ≫ prodSnd (min (Δ[n] : SSet.{u})) X = 𝟙 X :=
  Hom.ext rfl

/-- Every whole parameter section is monic for any original marked source and parameter vertex. -/
theorem parameterSection_mono (X : Marked.{u}) {n : ℕ}
    (v : (Δ[n] : SSet.{u}) _⦋0⦌) : Mono (parameterSection X v) := by
  refine ⟨fun {Z} f g h => ?_⟩
  have k := congrArg (fun q => q ≫ prodSnd (min (Δ[n] : SSet.{u})) X) h
  simpa only [Category.assoc, parameterSection_snd, Category.comp_id] using k

/-- The entire parameter section is natural in every original marked source map. -/
theorem parameterSection_natural {X Y : Marked.{u}} (f : X ⟶ Y) {n : ℕ}
    (v : (Δ[n] : SSet.{u}) _⦋0⦌) :
    parameterSection X v ≫ prodMap (𝟙 (min (Δ[n] : SSet.{u}))) f =
      f ≫ parameterSection Y v :=
  Hom.ext rfl

/-- Its actual one-simplex is the original marked source edge paired with the parameter degeneracy. -/
@[simp]
theorem parameterSection_app_one (X : Marked.{u}) {n : ℕ}
    (v : (Δ[n] : SSet.{u}) _⦋0⦌) (e : X.toSSet _⦋1⦌) :
    (parameterSection X v).hom.app (op ⦋1⦌) e = ((Δ[n] : SSet.{u}).σ (0 : Fin 1) v, e) := by
  apply Prod.ext
  · exact const_app_one (X := X) (Y := min (Δ[n] : SSet.{u})) v e
  · rfl

/-- The actual zero-parameter unit inverse is the section at its unique original vertex. -/
theorem zeroParameterUnitIso_inv_eq_section (X : Marked.{u})
    (v : (Δ[0] : SSet.{u}) _⦋0⦌) :
    (zeroParameterUnitIso .minimal X).inv = parameterSection X v := by
  apply (cancel_mono (zeroParameterUnitIso .minimal X).hom).mp
  rw [Iso.inv_hom_id]
  apply Hom.ext
  rfl

/-- Zero-parameter restriction to a chosen vertex is the same original marked section. -/
theorem zeroParameterSection_comp_map (X : Marked.{u}) {n : ℕ}
    (v : (Δ[n] : SSet.{u}) _⦋0⦌) :
    (zeroParameterUnitIso .minimal X).inv ≫
      prodMap (minimal.map (SSet.yonedaEquiv.symm v)) (𝟙 X) = parameterSection X v := by
  apply (cancel_epi (zeroParameterUnitIso .minimal X).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  apply Hom.ext
  ext m x
  apply Prod.ext
  · change (SSet.yonedaEquiv.symm v).app m x.1 = (SSet.const v).app m x.2
    rw [SSet.yonedaEquiv_symm_zero]
    rfl
  · rfl

end SSet.Marked
